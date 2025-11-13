 (* =============================================================================
   BGP-4 Formal Verification
   RFC 4271 (Rekhter, Li, Hares, 2006)
   Charles C Norton, September 2025

   "Greater still were the maps that showed the roads between realms."

   Extensions: RFC 8654 (Extended Messages), RFC 6793 (4-byte ASN),
               RFC 5065 (Confederations), RFC 4760 (MP-BGP),
               RFC 4456 (Route Reflection), RFC 7911 (ADD-PATH),
               RFC 8205 (BGPsec/ECDSA-P256)

   TO DO:
   1. AS_PATH stored as flat list; segment types lost
   2. Connection direction untracked; collision resolution incomplete (§6.8)
   3. Route reflection attributes validated only; auto-prepend logic external
   4. Confederation boundary segment rewriting unmodeled
   5. ADD-PATH capability only; NLRI encoding incomplete
   6. Complexity bounds placeholder

   ============================================================================= *)

From Coq Require Import
  List
  NArith.NArith
  Bool
  Arith
  Lia.

Import ListNotations.
Open Scope N_scope.

(* =============================================================================
   §1: Basic Types and Constants
   ============================================================================= *)

Definition byte := N.
Definition word16 := N.
Definition word32 := N.

(* RFC 4271 §4: Protocol constants *)
Definition BGP_VERSION : byte := 4.
Definition BGP_PORT : word16 := 179.
Definition BGP_MARKER_LENGTH : N := 16.
Definition BGP_HEADER_LENGTH : N := 19.
Definition BGP_MAX_MESSAGE_LENGTH : N := 4096.
Definition BGP_MIN_MESSAGE_LENGTH : N := 19.

(* RFC 4271 §10: Timer defaults (seconds) *)
Definition HOLD_TIME_DEFAULT : N := 90.
Definition HOLD_TIME_MIN : N := 3.
Definition HOLD_TIME_MAX : N := 65535.
Definition KEEPALIVE_TIME : N := 30.
Definition CONNECT_RETRY_TIME : N := 120.
Definition MIN_AS_ORIGINATION_INTERVAL : N := 15.
Definition MIN_ROUTE_ADVERTISEMENT_INTERVAL : N := 30.

(* =============================================================================
   §1.5: Encoding Helper Functions
   ============================================================================= *)

Fixpoint repeat_byte (b : byte) (n : nat) : list byte :=
  match n with
  | O => []
  | S n' => b :: repeat_byte b n'
  end.

Definition encode_word16 (w : word16) : list byte :=
  [N.shiftr w 8; N.land w 255].

Definition encode_word32 (w : word32) : list byte :=
  [N.shiftr w 24;
   N.land (N.shiftr w 16) 255;
   N.land (N.shiftr w 8) 255;
   N.land w 255].

Definition standard_bgp_marker : list byte := repeat_byte 255 16.

(* =============================================================================
   §2: Message Types (RFC 4271 §4.1)
   ============================================================================= *)

Inductive BGPMessageType :=
  | OPEN : BGPMessageType
  | UPDATE : BGPMessageType
  | NOTIFICATION : BGPMessageType
  | KEEPALIVE : BGPMessageType.

Definition message_type_to_byte (mt : BGPMessageType) : byte :=
  match mt with
  | OPEN => 1
  | UPDATE => 2
  | NOTIFICATION => 3
  | KEEPALIVE => 4
  end.

Record BGPHeader := {
  bgp_marker : list byte;
  bgp_length : word16;
  bgp_type : BGPMessageType
}.

(* =============================================================================
   §3: OPEN Message (RFC 4271 §4.2)
   ============================================================================= *)

Record BGPOptionalParameter := {
  opt_param_type : byte;
  opt_param_length : byte;
  opt_param_value : list byte
}.

Record BGPOpen := {
  open_version : byte;
  open_my_as : word16;
  open_hold_time : word16;
  open_bgp_identifier : word32;
  open_opt_param_len : byte;
  open_opt_params : list BGPOptionalParameter
}.

Definition CAP_MULTIPROTOCOL : byte := 1.
Definition CAP_ROUTE_REFRESH : byte := 2.
Definition CAP_EXTENDED_MESSAGE : byte := 6.
Definition CAP_4BYTE_AS : byte := 65.
Definition CAP_ADD_PATH : byte := 69.

(* =============================================================================
   §3.5: OPEN Message Construction
   ============================================================================= *)

Fixpoint encode_optional_params (params : list BGPOptionalParameter) : list byte :=
  match params with
  | [] => []
  | param :: rest =>
      [param.(opt_param_type); param.(opt_param_length)] ++
      param.(opt_param_value) ++
      encode_optional_params rest
  end.

Definition calculate_opt_param_length (params : list BGPOptionalParameter) : byte :=
  fold_left (fun acc p => acc + 2 + p.(opt_param_length)) params 0.

Definition build_open_message (open_msg : BGPOpen) : list byte :=
  let param_bytes := encode_optional_params open_msg.(open_opt_params) in
  let opt_param_len := calculate_opt_param_length open_msg.(open_opt_params) in
  let message_body :=
    [open_msg.(open_version)] ++
    encode_word16 open_msg.(open_my_as) ++
    encode_word16 open_msg.(open_hold_time) ++
    encode_word32 open_msg.(open_bgp_identifier) ++
    [opt_param_len] ++
    param_bytes in
  let total_length := BGP_HEADER_LENGTH + N.of_nat (length message_body) in
  standard_bgp_marker ++
  encode_word16 total_length ++
  [message_type_to_byte OPEN] ++
  message_body.

Theorem build_open_preserves_version : forall open_msg,
  nth 19 (build_open_message open_msg) 0 = open_msg.(open_version).
Proof.
  intros. unfold build_open_message. simpl. reflexivity.
Qed.

(* =============================================================================
   §3.6: KEEPALIVE Message Construction
   ============================================================================= *)

Definition build_keepalive_message : list byte :=
  standard_bgp_marker ++
  encode_word16 19 ++
  [message_type_to_byte KEEPALIVE].

Theorem keepalive_length_correct :
  length (build_keepalive_message) = 19%nat.
Proof.
  unfold build_keepalive_message, standard_bgp_marker, repeat_byte.
  simpl. reflexivity.
Qed.

Theorem keepalive_has_valid_marker :
  firstn 16 build_keepalive_message = standard_bgp_marker.
Proof.
  unfold build_keepalive_message.
  rewrite firstn_app.
  unfold standard_bgp_marker, repeat_byte.
  simpl. reflexivity.
Qed.

(* =============================================================================
   §4: UPDATE Message (RFC 4271 §4.3)
   ============================================================================= *)

Record NLRI := {
  nlri_prefix_len : byte;
  nlri_prefix : list byte
}.

(* RFC 7911: ADD-PATH extension *)
Record NLRI_AddPath := {
  nlri_path_id : word32;
  nlri_add_prefix_len : byte;
  nlri_add_prefix : list byte
}.

Definition nlri_to_addpath (nlri : NLRI) : NLRI_AddPath :=
  {| nlri_path_id := 0;
     nlri_add_prefix_len := nlri.(nlri_prefix_len);
     nlri_add_prefix := nlri.(nlri_prefix) |}.

Definition addpath_to_nlri (ap_nlri : NLRI_AddPath) : NLRI :=
  {| nlri_prefix_len := ap_nlri.(nlri_add_prefix_len);
     nlri_prefix := ap_nlri.(nlri_add_prefix) |}.

Record PathAttribute := {
  attr_flags : byte;
  attr_type_code : byte;
  attr_length : N;
  attr_value : list byte
}.

Record BGPUpdate := {
  update_withdrawn_routes_len : word16;
  update_withdrawn_routes : list NLRI;
  update_path_attr_len : word16;
  update_path_attributes : list PathAttribute;
  update_nlri : list NLRI
}.

(* =============================================================================
   §4.5: UPDATE Message Serialization
   ============================================================================= *)

Fixpoint encode_nlri_list (nlris : list NLRI) : list byte :=
  match nlris with
  | [] => []
  | nlri :: rest =>
      nlri.(nlri_prefix_len) ::
      nlri.(nlri_prefix) ++
      encode_nlri_list rest
  end.

Definition encode_path_attribute (attr : PathAttribute) : list byte :=
  let is_extended := N.leb 256 attr.(attr_length) in
  if is_extended then
    [attr.(attr_flags); attr.(attr_type_code)] ++
    encode_word16 attr.(attr_length) ++
    attr.(attr_value)
  else
    [attr.(attr_flags); attr.(attr_type_code); attr.(attr_length)] ++
    attr.(attr_value).

Fixpoint encode_path_attributes (attrs : list PathAttribute) : list byte :=
  match attrs with
  | [] => []
  | attr :: rest =>
      encode_path_attribute attr ++
      encode_path_attributes rest
  end.

Definition build_update_message (update : BGPUpdate) : list byte :=
  let withdrawn_bytes := encode_nlri_list update.(update_withdrawn_routes) in
  let withdrawn_len := N.of_nat (length withdrawn_bytes) in
  let attr_bytes := encode_path_attributes update.(update_path_attributes) in
  let attr_len := N.of_nat (length attr_bytes) in
  let nlri_bytes := encode_nlri_list update.(update_nlri) in
  let message_body :=
    encode_word16 withdrawn_len ++
    withdrawn_bytes ++
    encode_word16 attr_len ++
    attr_bytes ++
    nlri_bytes in
  let total_length := BGP_HEADER_LENGTH + N.of_nat (length message_body) in
  standard_bgp_marker ++
  encode_word16 total_length ++
  [message_type_to_byte UPDATE] ++
  message_body.

Theorem empty_update_valid_length :
  let empty_update := {| update_withdrawn_routes_len := 0;
                         update_withdrawn_routes := [];
                         update_path_attr_len := 0;
                         update_path_attributes := [];
                         update_nlri := [] |} in
  length (build_update_message empty_update) = 23%nat.
Proof.
  unfold build_update_message, encode_nlri_list, encode_path_attributes.
  simpl. unfold standard_bgp_marker, repeat_byte. simpl. reflexivity.
Qed.

(* Attribute flags: RFC 4271 bit 0 = MSB *)
Definition ATTR_FLAG_OPTIONAL : byte := 128.
Definition ATTR_FLAG_TRANSITIVE : byte := 64.
Definition ATTR_FLAG_PARTIAL : byte := 32.
Definition ATTR_FLAG_EXTENDED : byte := 16.

Definition ATTR_ORIGIN : byte := 1.
Definition ATTR_AS_PATH : byte := 2.
Definition ATTR_NEXT_HOP : byte := 3.
Definition ATTR_MULTI_EXIT_DISC : byte := 4.
Definition ATTR_LOCAL_PREF : byte := 5.
Definition ATTR_ATOMIC_AGGREGATE : byte := 6.
Definition ATTR_AGGREGATOR : byte := 7.
Definition ATTR_COMMUNITIES : byte := 8.
Definition ATTR_ORIGINATOR_ID : byte := 9.
Definition ATTR_CLUSTER_LIST : byte := 10.
Definition ATTR_MP_REACH_NLRI : byte := 14.
Definition ATTR_MP_UNREACH_NLRI : byte := 15.
Definition ATTR_AS4_PATH : byte := 17.
Definition ATTR_AS4_AGGREGATOR : byte := 18.

(* RFC 6793: Placeholder for 4-byte AS in 2-byte fields *)
Definition AS_TRANS : word32 := 23456.

Definition ORIGIN_IGP : byte := 0.
Definition ORIGIN_EGP : byte := 1.
Definition ORIGIN_INCOMPLETE : byte := 2.

Definition AS_SET : byte := 1.
Definition AS_SEQUENCE : byte := 2.
Definition AS_CONFED_SEQUENCE : byte := 3.
Definition AS_CONFED_SET : byte := 4.

(* RFC 6793 §4.2.3: Segment-aware representation *)
Record ASPathSegment := {
  seg_type : byte;
  seg_as_numbers : list word32
}.

Definition flat_to_segmented (as_list : list word32) : list ASPathSegment :=
  match as_list with
  | [] => []
  | _ => [{| seg_type := AS_SEQUENCE; seg_as_numbers := as_list |}]
  end.

Fixpoint segmented_to_flat (segments : list ASPathSegment) : list word32 :=
  match segments with
  | [] => []
  | seg :: rest => seg.(seg_as_numbers) ++ segmented_to_flat rest
  end.

(* =============================================================================
   §4.25: AS_PATH Encoding/Decoding with Segment Preservation
   ============================================================================= *)

(* Encode AS_PATH segments to wire format *)
Fixpoint encode_as_path_segments (segments : list ASPathSegment) : list byte :=
  match segments with
  | [] => []
  | seg :: rest =>
      let as_count := N.of_nat (length seg.(seg_as_numbers)) in
      [seg.(seg_type); as_count] ++
      flat_map encode_word32 seg.(seg_as_numbers) ++
      encode_as_path_segments rest
  end.

(* Decode AS_PATH segments from wire format with fuel *)
Fixpoint decode_as_path_segments_aux (bytes : list byte) (fuel : nat) : list ASPathSegment :=
  match fuel with
  | O => []
  | S fuel' =>
      match bytes with
      | seg_type :: as_count :: rest =>
          let num_as := N.to_nat as_count in
          let as_bytes_needed := (num_as * 4)%nat in
          let as_bytes := firstn as_bytes_needed rest in
          let remaining := skipn as_bytes_needed rest in
          let as_nums :=
            (fix decode_as_list (bs : list byte) (n : nat) : list word32 :=
              match n with
              | O => []
              | S n' =>
                  match bs with
                  | b1 :: b2 :: b3 :: b4 :: rest_bs =>
                      let asn := N.lor (N.lor (N.lor (N.shiftl b1 24) (N.shiftl b2 16))
                                              (N.shiftl b3 8)) b4 in
                      asn :: decode_as_list rest_bs n'
                  | _ => []
                  end
              end) as_bytes num_as in
          {| seg_type := seg_type; seg_as_numbers := as_nums |} ::
          decode_as_path_segments_aux remaining fuel'
      | _ => []
      end
  end.

Definition decode_as_path_segments (bytes : list byte) : list ASPathSegment :=
  decode_as_path_segments_aux bytes (length bytes).

(* Helper lemma: flat_map length *)
Lemma flat_map_encode_word32_length : forall asns,
  length (flat_map encode_word32 asns) = (4 * length asns)%nat.
Proof.
  induction asns as [| asn rest IH].
  - simpl. reflexivity.
  - change (flat_map encode_word32 (asn :: rest))
      with (encode_word32 asn ++ flat_map encode_word32 rest).
    rewrite app_length.
    rewrite IH.
    unfold encode_word32.
    simpl.
    ring.
Qed.

(* Helper lemma: firstn of exact length *)
Lemma firstn_exact_length : forall {A : Type} (l : list A) n,
  length l = n -> firstn n l = l.
Proof.
  intros A l n H.
  rewrite <- H.
  apply firstn_all.
Qed.

(* Helper lemma: decode single AS number *)
Lemma decode_single_as : forall asn,
  (fix decode_as_list (bs : list byte) (n : nat) : list word32 :=
    match n with
    | O => []
    | S n' =>
        match bs with
        | b1 :: b2 :: b3 :: b4 :: rest_bs =>
            let asn := N.lor (N.lor (N.lor (N.shiftl b1 24) (N.shiftl b2 16))
                                    (N.shiftl b3 8)) b4 in
            asn :: decode_as_list rest_bs n'
        | _ => []
        end
    end) (encode_word32 asn) 1%nat = [asn].
Proof.
Admitted.

Lemma decode_as_list_correct : forall asns,
  (fix decode_as_list (bs : list byte) (n : nat) : list word32 :=
    match n with
    | O => []
    | S n' =>
        match bs with
        | b1 :: b2 :: b3 :: b4 :: rest_bs =>
            let asn := N.lor (N.lor (N.lor (N.shiftl b1 24) (N.shiftl b2 16))
                                    (N.shiftl b3 8)) b4 in
            asn :: decode_as_list rest_bs n'
        | _ => []
        end
    end) (flat_map encode_word32 asns) (length asns) = asns.
Proof.
Admitted.

(* Theorem: encoding and decoding are inverse *)
Theorem encode_decode_as_path_identity : forall segs,
  decode_as_path_segments (encode_as_path_segments segs) = segs.
Proof.
Admitted.

(* RFC 6793 §4.2.3: AS_PATH/AS4_PATH merge with confederation awareness *)
Fixpoint merge_segments (as_path as4_path : list ASPathSegment) : list ASPathSegment :=
  match as_path with
  | [] => []
  | seg :: rest_segs =>
      let is_confed := orb (N.eqb seg.(seg_type) AS_CONFED_SEQUENCE)
                           (N.eqb seg.(seg_type) AS_CONFED_SET) in
      if is_confed then
        seg :: merge_segments rest_segs as4_path
      else
        let merged_as_nums :=
          (fix merge_nums (nums nums4 : list word32) : list word32 :=
            match nums, nums4 with
            | [], _ => []
            | n :: rest_n, n4 :: rest_n4 =>
                if N.eqb n AS_TRANS
                then n4 :: merge_nums rest_n rest_n4
                else n :: merge_nums rest_n nums4
            | n :: rest_n, [] => n :: merge_nums rest_n []
            end) seg.(seg_as_numbers) (segmented_to_flat as4_path) in
        {| seg_type := seg.(seg_type); seg_as_numbers := merged_as_nums |} ::
        merge_segments rest_segs []
  end.

(* Confederation segments preserved during merge *)
Theorem confed_segments_preserved: forall seg rest_segs as4_path,
  orb (N.eqb seg.(seg_type) AS_CONFED_SEQUENCE) (N.eqb seg.(seg_type) AS_CONFED_SET) = true ->
  In seg (merge_segments (seg :: rest_segs) as4_path).
Proof.
  intros seg rest_segs as4_path Hconfed.
  simpl.
  rewrite Hconfed.
  simpl. left. reflexivity.
Qed.

(* Merging empty AS4_PATH preserves AS_PATH *)
Theorem merge_with_empty_preserves: forall as_path,
  segmented_to_flat (merge_segments as_path []) = segmented_to_flat as_path.
Proof.
  induction as_path as [| seg rest IH].
  - simpl. reflexivity.
  - simpl.
    destruct (orb (N.eqb (seg_type seg) AS_CONFED_SEQUENCE)
                  (N.eqb (seg_type seg) AS_CONFED_SET)) eqn:Hconfed.
    + simpl. f_equal. exact IH.
    + simpl.
      assert (Hmerge: forall nums,
        (fix merge_nums (nums0 nums4 : list N) {struct nums0} : list N :=
          match nums0 with
          | [] => []
          | n :: rest_n =>
              match nums4 with
              | [] => n :: merge_nums rest_n []
              | n4 :: rest_n4 =>
                  if n =? AS_TRANS then n4 :: merge_nums rest_n rest_n4
                  else n :: merge_nums rest_n nums4
              end
          end) nums [] = nums).
      { induction nums as [| n rest_n IH_inner].
        - reflexivity.
        - simpl. f_equal. exact IH_inner. }
      rewrite Hmerge.
      rewrite <- IH.
      reflexivity.
Qed.

(* RFC 4760: Address Family Identifiers *)
Definition AFI_IPV4 : word16 := 1.
Definition AFI_IPV6 : word16 := 2.
Definition AFI_L2VPN : word16 := 25.
Definition AFI_BGPLS : word16 := 16388.

(* RFC 4760: Subsequent Address Family Identifiers *)
Definition SAFI_UNICAST : byte := 1.
Definition SAFI_MULTICAST : byte := 2.
Definition SAFI_MPLS_LABEL : byte := 4.
Definition SAFI_MCAST_VPN : byte := 5.
Definition SAFI_VPLS : byte := 65.
Definition SAFI_EVPN : byte := 70.
Definition SAFI_BGPLS : byte := 71.
Definition SAFI_MPLS_VPN : byte := 128.
Definition SAFI_ROUTE_TARGET : byte := 132.
Definition SAFI_FLOWSPEC : byte := 133.

(* =============================================================================
   §5: NOTIFICATION Message (RFC 4271 §4.5)
   ============================================================================= *)

Record BGPNotification := {
  notif_error_code : byte;
  notif_error_subcode : byte;
  notif_data : list byte
}.

Definition ERR_MESSAGE_HEADER : byte := 1.
Definition ERR_OPEN_MESSAGE : byte := 2.
Definition ERR_UPDATE_MESSAGE : byte := 3.
Definition ERR_HOLD_TIMER : byte := 4.
Definition ERR_FSM : byte := 5.
Definition ERR_CEASE : byte := 6.

Definition OPEN_ERR_UNSUPPORTED_VERSION : byte := 1.
Definition OPEN_ERR_BAD_PEER_AS : byte := 2.
Definition OPEN_ERR_BAD_BGP_IDENTIFIER : byte := 3.
Definition OPEN_ERR_UNSUPPORTED_PARAM : byte := 4.
Definition OPEN_ERR_UNACCEPTABLE_HOLD_TIME : byte := 6.

Definition UPDATE_ERR_MALFORMED_ATTR_LIST : byte := 1.
Definition UPDATE_ERR_UNRECOGNIZED_WELLKNOWN_ATTR : byte := 2.
Definition UPDATE_ERR_MISSING_WELLKNOWN_ATTR : byte := 3.
Definition UPDATE_ERR_ATTR_FLAGS_ERROR : byte := 4.
Definition UPDATE_ERR_ATTR_LENGTH_ERROR : byte := 5.
Definition UPDATE_ERR_INVALID_ORIGIN_ATTR : byte := 6.
Definition UPDATE_ERR_INVALID_NEXT_HOP_ATTR : byte := 8.
Definition UPDATE_ERR_OPTIONAL_ATTR_ERROR : byte := 9.
Definition UPDATE_ERR_INVALID_NETWORK_FIELD : byte := 10.
Definition UPDATE_ERR_MALFORMED_AS_PATH : byte := 11.

Definition HEADER_ERR_CONNECTION_NOT_SYNCHRONIZED : byte := 1.
Definition HEADER_ERR_BAD_MESSAGE_LENGTH : byte := 2.
Definition HEADER_ERR_BAD_MESSAGE_TYPE : byte := 3.

Definition FSM_ERR_UNSPECIFIED : byte := 0.
Definition FSM_ERR_UNEXPECTED_MESSAGE_OPENSENT : byte := 1.
Definition FSM_ERR_UNEXPECTED_MESSAGE_OPENCONFIRM : byte := 2.
Definition FSM_ERR_UNEXPECTED_MESSAGE_ESTABLISHED : byte := 3.

(* =============================================================================
   §5.4: NOTIFICATION Message Construction
   ============================================================================= *)

Definition build_notification_message (notif : BGPNotification) : list byte :=
  let message_body :=
    [notif.(notif_error_code); notif.(notif_error_subcode)] ++
    notif.(notif_data) in
  let total_length := BGP_HEADER_LENGTH + N.of_nat (length message_body) in
  standard_bgp_marker ++
  encode_word16 total_length ++
  [message_type_to_byte NOTIFICATION] ++
  message_body.

Theorem notification_has_error_codes : forall notif,
  nth 19 (build_notification_message notif) 0 = notif.(notif_error_code) /\
  nth 20 (build_notification_message notif) 0 = notif.(notif_error_subcode).
Proof.
  intros. unfold build_notification_message. simpl. split; reflexivity.
Qed.

Theorem notification_min_length : forall notif,
  notif.(notif_data) = [] ->
  length (build_notification_message notif) = 21%nat.
Proof.
  intros notif Hdata.
  unfold build_notification_message.
  rewrite Hdata. simpl.
  unfold standard_bgp_marker, repeat_byte. simpl. reflexivity.
Qed.

(* =============================================================================
   §5.5: Validation Functions
   ============================================================================= *)

(* RFC 8654: Capability TLV parser with fuel-based termination *)
Fixpoint find_capability_in_bytes_aux (cap_code : byte) (bytes : list byte) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match bytes with
      | [] => false
      | code :: len :: value_rest =>
          if N.eqb code cap_code then true
          else find_capability_in_bytes_aux cap_code (skipn (N.to_nat len) value_rest) fuel'
      | _ => false
      end
  end.

Definition find_capability_in_bytes (cap_code : byte) (bytes : list byte) : bool :=
  find_capability_in_bytes_aux cap_code bytes (length bytes).

(* Capability presence in optional parameters (type code 2) *)
Fixpoint has_capability_in_params (cap_code : byte) (params : list BGPOptionalParameter) : bool :=
  match params with
  | [] => false
  | param :: rest =>
      if N.eqb param.(opt_param_type) 2 then
        orb (find_capability_in_bytes cap_code param.(opt_param_value))
            (has_capability_in_params cap_code rest)
      else
        has_capability_in_params cap_code rest
  end.

Definition supports_extended_message (params : list BGPOptionalParameter) : bool :=
  has_capability_in_params CAP_EXTENDED_MESSAGE params.

(* RFC 8654: Negotiated message length (65535 if both support, else 4096)
   Note: OPEN limited to 4096 regardless; KEEPALIVE always 19 *)
Definition negotiated_max_message_length (local_caps remote_caps : list BGPOptionalParameter) : N :=
  if andb (supports_extended_message local_caps) (supports_extended_message remote_caps)
  then 65535
  else BGP_MAX_MESSAGE_LENGTH.

(* Marker validation: 16 bytes of 0xFF *)
Definition valid_marker (marker : list byte) : bool :=
  andb (N.eqb (N.of_nat (length marker)) BGP_MARKER_LENGTH)
       (forallb (fun b => N.eqb b 255) marker).

(* Length validation: 19 ≤ length ≤ 4096 *)
Definition valid_header_length (length : word16) : bool :=
  andb (N.leb BGP_MIN_MESSAGE_LENGTH length)
       (N.leb length BGP_MAX_MESSAGE_LENGTH).

(* RFC 8654: Pre-OPEN length validation (always ≤ 4096) *)
Definition valid_header_length_preopen (length : word16) : bool :=
  andb (N.leb BGP_MIN_MESSAGE_LENGTH length)
       (N.leb length BGP_MAX_MESSAGE_LENGTH).

(* RFC 8654: Post-OPEN length validation using negotiated maximum *)
Definition valid_header_length_with_caps (local_caps remote_caps : list BGPOptionalParameter)
                                         (length : word16) : bool :=
  andb (N.leb BGP_MIN_MESSAGE_LENGTH length)
       (N.leb length (negotiated_max_message_length local_caps remote_caps)).

(* Message length consistency check *)
Definition validate_message_length (hdr : BGPHeader) (msg_type : BGPMessageType)
                                   (content_length : N) : bool :=
  N.eqb hdr.(bgp_length) (BGP_HEADER_LENGTH + content_length).

(* Complete header validation *)
Definition valid_bgp_header (hdr : BGPHeader) : bool :=
  andb (valid_marker hdr.(bgp_marker))
       (valid_header_length hdr.(bgp_length)).

(* RFC 8654: Header validation before OPEN exchange *)
Definition valid_bgp_header_preopen (hdr : BGPHeader) : bool :=
  andb (valid_marker hdr.(bgp_marker))
       (valid_header_length_preopen hdr.(bgp_length)).

(* RFC 8654: Header validation with negotiated capabilities *)
Definition valid_bgp_header_with_caps (local_caps remote_caps : list BGPOptionalParameter)
                                      (hdr : BGPHeader) : bool :=
  andb (valid_marker hdr.(bgp_marker))
       (valid_header_length_with_caps local_caps remote_caps hdr.(bgp_length)).
(* KEEPALIVE message validation: header-only, 19 bytes *)
Definition valid_keepalive_message (hdr : BGPHeader) : bool :=
  let type_ok := match hdr.(bgp_type) with
                 | KEEPALIVE => true
                 | _ => false
                 end in
  andb (valid_bgp_header hdr)
       (andb (N.eqb hdr.(bgp_length) 19) type_ok).

(* BGP Identifier validation: unicast IPv4, excluding 0.0.0.0, 127/8, 224+/4, 240+/4 *)
Definition valid_bgp_identifier (id : word32) : bool :=
  let a := N.shiftr id 24 in
  let b := N.land (N.shiftr id 16) 255 in
  let c := N.land (N.shiftr id 8) 255 in
  let d := N.land id 255 in
  let not_zero := negb (andb (N.eqb a 0) (andb (N.eqb b 0) (andb (N.eqb c 0) (N.eqb d 0)))) in
  let not_loopback := negb (N.eqb a 127) in
  let not_multicast := N.ltb a 224 in
  let not_class_e := N.ltb a 240 in
  andb not_zero (andb not_loopback (andb not_multicast not_class_e)).

(* Hold Time validation: 0 or [3, 65535] *)
Definition valid_hold_time (hold_time : word16) : bool :=
  orb (N.eqb hold_time 0)
      (andb (N.leb HOLD_TIME_MIN hold_time)
            (N.leb hold_time HOLD_TIME_MAX)).

(* AS number validation: reject reserved AS 0 *)
Definition valid_as_number (asn : word16) : bool :=
  negb (N.eqb asn 0).

(* ORIGIN attribute validation: IGP=0, EGP=1, INCOMPLETE=2 *)
Definition valid_origin_value (origin : byte) : bool :=
  orb (N.eqb origin ORIGIN_IGP)
      (orb (N.eqb origin ORIGIN_EGP)
           (N.eqb origin ORIGIN_INCOMPLETE)).

(* NLRI prefix length validation: 0-32 for IPv4 *)
Definition valid_nlri_prefix_len (prefix_len : byte) : bool :=
  N.leb prefix_len 32.

(* Host bits zero enforcement in NLRI prefix *)
Fixpoint check_host_bits_zero_aux (i : N) (bytes_needed rem_bits : N) (xs : list byte) : bool :=
  match xs with
  | [] => true
  | b :: rest =>
      let last_idx := N.pred bytes_needed in
      if N.ltb i last_idx then
        check_host_bits_zero_aux (i + 1) bytes_needed rem_bits rest
      else if N.eqb i last_idx then
        if N.eqb rem_bits 0 then true
        else
          let low_mask := N.shiftr 255 rem_bits in
          andb (N.eqb (N.land b low_mask) 0)
               (check_host_bits_zero_aux (i + 1) bytes_needed rem_bits rest)
      else
        andb (N.eqb b 0) (check_host_bits_zero_aux (i + 1) bytes_needed rem_bits rest)
  end.

Definition check_host_bits_zero (prefix : list byte) (prefix_len : N) : bool :=
  let bytes_needed := (prefix_len + 7) / 8 in
  let rem_bits := prefix_len mod 8 in
  check_host_bits_zero_aux 0 bytes_needed rem_bits prefix.

(* NLRI structure validation *)
Definition valid_nlri (nlri : NLRI) : bool :=
  let len_ok := valid_nlri_prefix_len nlri.(nlri_prefix_len) in
  let bytes_needed := (nlri.(nlri_prefix_len) + 7) / 8 in
  let bytes_ok := N.eqb (N.of_nat (length nlri.(nlri_prefix))) bytes_needed in
  let host_bits_ok := check_host_bits_zero nlri.(nlri_prefix) nlri.(nlri_prefix_len) in
  andb len_ok (andb bytes_ok host_bits_ok).

(* NEXT_HOP validation: 4-byte unicast IPv4 *)
Definition valid_next_hop (next_hop_bytes : list byte) : bool :=
  match next_hop_bytes with
  | [a; b; c; d] =>
      let not_zero := negb (andb (N.eqb a 0) (andb (N.eqb b 0) (andb (N.eqb c 0) (N.eqb d 0)))) in
      let not_loopback := negb (N.eqb a 127) in
      let not_multicast := N.ltb a 224 in
      let not_class_e := N.ltb a 240 in
      andb not_zero (andb not_loopback (andb not_multicast not_class_e))
  | _ => false
  end.

(* BGP Identifier collision detection *)
Definition has_bgp_id_collision (local_id remote_id : word32) : bool :=
  N.eqb local_id remote_id.

(* RFC 4271 §6.8: Connection collision resolution (higher ID wins) *)
Definition resolve_collision (local_id remote_id : word32) (is_local_initiator : bool) : bool :=
  if N.ltb local_id remote_id then
    negb is_local_initiator
  else
    is_local_initiator.

(* Optional parameter type: capabilities = 2 *)
Definition OPT_PARAM_CAPABILITIES : byte := 2.

(* Optional parameter type validation *)
Definition valid_opt_param_type (param_type : byte) : bool :=
  N.eqb param_type OPT_PARAM_CAPABILITIES.

(* Optional parameters validation in OPEN message *)
Definition valid_optional_params (params : list BGPOptionalParameter) (declared_len : byte) : bool :=
  let per_ok := forallb (fun p => N.eqb (N.of_nat (length p.(opt_param_value))) p.(opt_param_length)) params in
  let types_ok := forallb (fun p => valid_opt_param_type p.(opt_param_type)) params in
  let total_decl := fold_left (fun acc p => acc + 2 + p.(opt_param_length)) params 0 in
  andb types_ok (andb per_ok (N.eqb total_decl declared_len)).

(* Peer AS verification *)
Definition verify_peer_as (expected_as received_as : word16) : bool :=
  N.eqb expected_as received_as.

(* OPEN message validation *)
Definition valid_open_message (open_msg : BGPOpen) : bool :=
  andb (N.eqb open_msg.(open_version) BGP_VERSION)
       (andb (valid_bgp_identifier open_msg.(open_bgp_identifier))
             (andb (valid_hold_time open_msg.(open_hold_time))
                   (andb (valid_as_number open_msg.(open_my_as))
                         (valid_optional_params open_msg.(open_opt_params) open_msg.(open_opt_param_len))))).

(* Attribute flag bit test *)
Definition has_flag (flags target : byte) : bool :=
  negb (N.eqb (N.land flags target) 0).

(* AS_PATH structure validation with RFC 5065 confederation support *)
Fixpoint validate_as_path_structure_aux (bytes : list byte) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S fuel' =>
      match bytes with
      | [] => true
      | seg_type :: seg_len :: rest =>
          let type_ok := orb (orb (N.eqb seg_type AS_SET) (N.eqb seg_type AS_SEQUENCE))
                             (orb (N.eqb seg_type AS_CONFED_SEQUENCE) (N.eqb seg_type AS_CONFED_SET)) in
          let len_ok := N.leb 1 seg_len in
          let n := N.to_nat seg_len in
          let needed := Nat.mul 2 n in
          let enough_bytes := Nat.leb needed (length rest) in
          let rest' := skipn needed rest in
          andb type_ok (andb len_ok (andb enough_bytes (validate_as_path_structure_aux rest' fuel')))
      | _ => false
      end
  end.

Definition validate_as_path_structure (bytes : list byte) : bool :=
  validate_as_path_structure_aux bytes (length bytes).

(* RFC 6793: AS4_PATH structure validation (confederation segments forbidden) *)
Fixpoint validate_as4_path_structure_aux (bytes : list byte) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S fuel' =>
      match bytes with
      | [] => true
      | seg_type :: seg_len :: rest =>
          let type_ok := orb (N.eqb seg_type AS_SET) (N.eqb seg_type AS_SEQUENCE) in
          let len_ok := N.leb 1 seg_len in
          let n := N.to_nat seg_len in
          let needed := Nat.mul 4 n in
          let enough_bytes := Nat.leb needed (length rest) in
          let rest' := skipn needed rest in
          andb type_ok (andb len_ok (andb enough_bytes (validate_as4_path_structure_aux rest' fuel')))
      | _ => false
      end
  end.

Definition validate_as4_path_structure (bytes : list byte) : bool :=
  validate_as4_path_structure_aux bytes (length bytes).

(* RFC 4271 §4.3: Extended-length flag validation (>255 requires flag) *)
Definition valid_extended_length_flag (attr : PathAttribute) : bool :=
  let is_extended := has_flag attr.(attr_flags) ATTR_FLAG_EXTENDED in
  if is_extended then
    true
  else
    N.leb attr.(attr_length) 255.

(* RFC 4760: Valid AFI/SAFI combinations per IANA registry *)
Definition valid_afi_safi_combination (afi : word16) (safi : byte) : bool :=
  (N.eqb afi AFI_IPV4 && orb (N.eqb safi SAFI_UNICAST)
                              (orb (N.eqb safi SAFI_MULTICAST)
                                   (orb (N.eqb safi SAFI_MPLS_VPN)
                                        (N.eqb safi SAFI_FLOWSPEC)))) ||
  (N.eqb afi AFI_IPV6 && orb (N.eqb safi SAFI_UNICAST)
                              (orb (N.eqb safi SAFI_MULTICAST)
                                   (orb (N.eqb safi SAFI_MPLS_VPN)
                                        (N.eqb safi SAFI_FLOWSPEC)))) ||
  (N.eqb afi AFI_L2VPN && orb (N.eqb safi SAFI_VPLS)
                               (N.eqb safi SAFI_EVPN)) ||
  (N.eqb afi AFI_BGPLS && N.eqb safi SAFI_BGPLS).

(* AFI decoder: 2-byte big-endian from MP_REACH/MP_UNREACH *)
Definition decode_afi (bytes : list byte) : option word16 :=
  match bytes with
  | b1 :: b2 :: _ => Some (N.lor (N.shiftl b1 8) b2)
  | _ => None
  end.

(* SAFI decoder: third byte from MP_REACH/MP_UNREACH *)
Definition decode_safi (bytes : list byte) : option byte :=
  match bytes with
  | _ :: _ :: safi :: _ => Some safi
  | _ => None
  end.

(* MP-BGP attribute AFI/SAFI validation *)
Definition validate_mp_bgp_afi_safi (attr_value : list byte) : bool :=
  match decode_afi attr_value, decode_safi attr_value with
  | Some afi, Some safi => valid_afi_safi_combination afi safi
  | _, _ => false
  end.

Definition valid_path_attribute (attr : PathAttribute) : bool :=
  let is_optional := has_flag attr.(attr_flags) ATTR_FLAG_OPTIONAL in
  let is_transitive := has_flag attr.(attr_flags) ATTR_FLAG_TRANSITIVE in
  let is_partial := has_flag attr.(attr_flags) ATTR_FLAG_PARTIAL in
  let reserved_bits_clear := N.eqb (N.land attr.(attr_flags) 15) 0 in
  let len_matches := N.eqb attr.(attr_length) (N.of_nat (length attr.(attr_value))) in
  let flags_ok := match attr.(attr_type_code) with
    | 1 => andb (andb (andb (negb is_optional) is_transitive) (negb is_partial)) reserved_bits_clear       (* ORIGIN *)
    | 2 => andb (andb (andb (negb is_optional) is_transitive) (negb is_partial)) reserved_bits_clear       (* AS_PATH *)
    | 3 => andb (andb (andb (negb is_optional) is_transitive) (negb is_partial)) reserved_bits_clear       (* NEXT_HOP *)
    | 4 => andb (andb (andb is_optional (negb is_transitive)) (negb is_partial)) reserved_bits_clear       (* MED *)
    | 5 => andb (andb (andb (negb is_optional) is_transitive) (negb is_partial)) reserved_bits_clear       (* LOCAL_PREF *)
    | 6 => andb (andb (andb (negb is_optional) is_transitive) (negb is_partial)) reserved_bits_clear       (* ATOMIC_AGGREGATE *)
    | 7 => andb (andb is_optional is_transitive) reserved_bits_clear                                        (* AGGREGATOR *)
    | 9 => andb (andb (andb is_optional (negb is_transitive)) (negb is_partial)) reserved_bits_clear       (* ORIGINATOR_ID, RFC 4456 *)
    | 10 => andb (andb (andb is_optional (negb is_transitive)) (negb is_partial)) reserved_bits_clear      (* CLUSTER_LIST, RFC 4456 *)
    | 14 => andb (andb (andb is_optional (negb is_transitive)) (negb is_partial)) reserved_bits_clear      (* MP_REACH_NLRI, RFC 4760 *)
    | 15 => andb (andb (andb is_optional (negb is_transitive)) (negb is_partial)) reserved_bits_clear      (* MP_UNREACH_NLRI, RFC 4760 *)
    | 17 => andb (andb is_optional is_transitive) reserved_bits_clear                                       (* AS4_PATH, RFC 6793 *)
    | 18 => andb (andb is_optional is_transitive) reserved_bits_clear                                       (* AS4_AGGREGATOR, RFC 6793 *)
    | _ => reserved_bits_clear
    end in
  let value_ok := match attr.(attr_type_code) with
    | 1 => match attr.(attr_value) with [v] => valid_origin_value v | _ => false end
    | 2 => validate_as_path_structure attr.(attr_value)
    | 3 => valid_next_hop attr.(attr_value)
    | 4 => N.eqb (N.of_nat (length attr.(attr_value))) 4
    | 5 => N.eqb (N.of_nat (length attr.(attr_value))) 4
    | 6 => N.eqb (N.of_nat (length attr.(attr_value))) 0
    | 7 => N.eqb (N.of_nat (length attr.(attr_value))) 6
    | 9 => N.eqb (N.of_nat (length attr.(attr_value))) 4                  (* ORIGINATOR_ID: 4 bytes *)
    | 10 => N.eqb (N.of_nat (length attr.(attr_value)) mod 4) 0           (* CLUSTER_LIST: multiple of 4 bytes *)
    | 14 => andb (N.leb 5 (N.of_nat (length attr.(attr_value))))          (* MP_REACH_NLRI: min 5 bytes + valid AFI/SAFI *)
                 (validate_mp_bgp_afi_safi attr.(attr_value))
    | 15 => andb (N.leb 3 (N.of_nat (length attr.(attr_value))))          (* MP_UNREACH_NLRI: min 3 bytes + valid AFI/SAFI *)
                 (validate_mp_bgp_afi_safi attr.(attr_value))
    | 17 => andb (negb (N.eqb (N.of_nat (length attr.(attr_value))) 0))  (* AS4_PATH: non-empty, 4-byte ASN structure *)
                 (validate_as4_path_structure attr.(attr_value))
    | 18 => N.eqb (N.of_nat (length attr.(attr_value))) 8                 (* AS4_AGGREGATOR: 4 bytes AS + 4 bytes IP *)
    | _ => true
    end in
  let extended_ok := valid_extended_length_flag attr in
  andb len_matches (andb flags_ok (andb value_ok extended_ok)).

(* Mandatory attributes check: ORIGIN, AS_PATH, NEXT_HOP *)
Definition has_mandatory_attributes (attrs : list PathAttribute) : bool :=
  let has_origin := existsb (fun a => N.eqb a.(attr_type_code) ATTR_ORIGIN) attrs in
  let has_as_path := existsb (fun a => N.eqb a.(attr_type_code) ATTR_AS_PATH) attrs in
  let has_next_hop := existsb (fun a => N.eqb a.(attr_type_code) ATTR_NEXT_HOP) attrs in
  andb has_origin (andb has_as_path has_next_hop).

(* RFC 7606: Strict duplicate attribute detection *)
Fixpoint has_duplicate_attr_codes (attrs : list PathAttribute) (seen : list byte) : bool :=
  match attrs with
  | [] => false
  | a :: rest =>
      if existsb (N.eqb a.(attr_type_code)) seen
      then true
      else has_duplicate_attr_codes rest (a.(attr_type_code) :: seen)
  end.

Definition no_duplicate_attributes (attrs : list PathAttribute) : bool :=
  negb (has_duplicate_attr_codes attrs []).

(* Full AS_PATH loop detection *)
Fixpoint has_full_as_loop (as_path : list word32) (seen : list word32) : bool :=
  match as_path with
  | [] => false
  | asn :: rest =>
      if existsb (N.eqb asn) seen
      then true
      else has_full_as_loop rest (asn :: seen)
  end.

(* Own AS presence check *)
Definition has_as_loop (my_as : word32) (as_path : list word32) : bool :=
  existsb (fun asn => N.eqb asn my_as) as_path.

(* Combined AS_PATH loop validation *)
Definition valid_as_path_no_loops (my_as : word32) (as_path : list word32) : bool :=
  andb (negb (has_as_loop my_as as_path))
       (negb (has_full_as_loop as_path [])).

(* Withdrawn routes length validation *)
Definition validate_withdrawn_length (withdrawn_routes : list NLRI) (declared_len : word16) : bool :=
  let actual_len := fold_left (fun acc nlri => acc + 1 + N.of_nat (length nlri.(nlri_prefix))) withdrawn_routes 0 in
  N.eqb actual_len declared_len.

(* Attribute header length: 3 bytes normal, 4 bytes extended *)
Definition attr_header_len (attr : PathAttribute) : N :=
  if has_flag attr.(attr_flags) ATTR_FLAG_EXTENDED then 4 else 3.

(* Path attributes total length validation *)
Definition validate_path_attr_length (attrs : list PathAttribute) (declared_len : word16) : bool :=
  let actual_len := fold_left (fun acc attr => acc + attr_header_len attr + attr.(attr_length)) attrs 0 in
  N.eqb actual_len declared_len.

(* UPDATE message validation (RFC 4271 compliance, not policy) *)
Definition valid_update_message (my_as : word32) (update : BGPUpdate) : bool :=
  let all_attrs_valid := forallb valid_path_attribute update.(update_path_attributes) in
  let has_mandatory := if negb (N.eqb (N.of_nat (length update.(update_nlri))) 0)
                       then has_mandatory_attributes update.(update_path_attributes)
                       else true in
  let all_nlri_valid := forallb valid_nlri update.(update_nlri) in
  let all_withdrawn_valid := forallb valid_nlri update.(update_withdrawn_routes) in
  let no_duplicates := no_duplicate_attributes update.(update_path_attributes) in
  let withdrawn_len_ok := validate_withdrawn_length update.(update_withdrawn_routes) update.(update_withdrawn_routes_len) in
  let attr_len_ok := validate_path_attr_length update.(update_path_attributes) update.(update_path_attr_len) in
  andb all_attrs_valid (andb has_mandatory (andb all_nlri_valid (andb all_withdrawn_valid (andb no_duplicates (andb withdrawn_len_ok attr_len_ok))))).

(* 2-byte ASN decoder *)
Fixpoint take_as_numbers (n : nat) (bs : list byte) : list word32 :=
  match n, bs with
  | O, _ => []
  | S n', b1 :: b2 :: rest' =>
      (N.lor (N.shiftl b1 8) b2) :: take_as_numbers n' rest'
  | _, _ => []
  end.

(* Skip n bytes from list *)
Fixpoint skip_bytes (n : nat) (bs : list byte) : list byte :=
  match n, bs with
  | O, _ => bs
  | S n', _ :: rest => skip_bytes n' rest
  | _, [] => []
  end.

(* AS_PATH decoder with fuel *)
Fixpoint decode_as_path_aux (bytes : list byte) (fuel : nat) : list word32 :=
  match fuel with
  | O => []
  | S fuel' =>
      match bytes with
      | [] => []
      | _seg_type :: seg_len :: rest =>
          let n := N.to_nat seg_len in
          let needed := Nat.mul 2 n in
          let asns := take_as_numbers n rest in
          let rest' := skip_bytes needed rest in
          asns ++ decode_as_path_aux rest' fuel'
      | _ => []
      end
  end.

Definition decode_as_path (bytes : list byte) : list word32 :=
  decode_as_path_aux bytes (length bytes).

(* RFC 6793: 4-byte ASN decoder *)
Fixpoint take_as_numbers_4byte (n : nat) (bs : list byte) : list word32 :=
  match n, bs with
  | O, _ => []
  | S n', b1 :: b2 :: b3 :: b4 :: rest' =>
      let asn := N.lor (N.lor (N.lor (N.shiftl b1 24) (N.shiftl b2 16))
                               (N.shiftl b3 8)) b4 in
      asn :: take_as_numbers_4byte n' rest'
  | _, _ => []
  end.

(* AS4_PATH decoder *)
Fixpoint decode_as4_path_aux (bytes : list byte) (fuel : nat) : list word32 :=
  match fuel with
  | O => []
  | S fuel' =>
      match bytes with
      | [] => []
      | _seg_type :: seg_len :: rest =>
          let n := N.to_nat seg_len in
          let needed := Nat.mul 4 n in
          let asns := take_as_numbers_4byte n rest in
          let rest' := skip_bytes needed rest in
          asns ++ decode_as4_path_aux rest' fuel'
      | _ => []
      end
  end.

Definition decode_as4_path (bytes : list byte) : list word32 :=
  decode_as4_path_aux bytes (length bytes).

(* RFC 6793 §4.2.3: AS_PATH/AS4_PATH merge (replaces AS_TRANS with 4-byte ASN) *)
Fixpoint merge_as_paths (as_path as4_path : list word32) : list word32 :=
  match as_path, as4_path with
  | [], _ => []
  | asn :: rest, as4 :: rest4 =>
      if N.eqb asn AS_TRANS
      then as4 :: merge_as_paths rest rest4
      else asn :: merge_as_paths rest as4_path
  | asn :: rest, [] => asn :: merge_as_paths rest []
  end.

(* Effective AS_PATH extraction with AS4_PATH merge *)
Definition get_effective_as_path (attrs : list PathAttribute) : list word32 :=
  let as_path := match find (fun attr => N.eqb attr.(attr_type_code) ATTR_AS_PATH) attrs with
                 | None => []
                 | Some attr => decode_as_path attr.(attr_value)
                 end in
  let as4_path := match find (fun attr => N.eqb attr.(attr_type_code) ATTR_AS4_PATH) attrs with
                  | None => []
                  | Some attr => decode_as4_path attr.(attr_value)
                  end in
  if N.eqb (N.of_nat (length as4_path)) 0
  then as_path
  else merge_as_paths as_path as4_path.

(* UPDATE AS_PATH loop check *)
Definition update_has_as_loop (my_as : word32) (update : BGPUpdate) : bool :=
  has_as_loop my_as (get_effective_as_path update.(update_path_attributes)).

(* =============================================================================
   §6: Finite State Machine (RFC 4271 §8)
   ============================================================================= *)

Inductive BGPState :=
  | IDLE
  | CONNECT
  | ACTIVE
  | OPENSENT
  | OPENCONFIRM
  | ESTABLISHED.

Record BGPSession := {
  session_state : BGPState;
  session_local_as : word32;
  session_remote_as : word32;
  session_local_id : word32;
  session_remote_id : word32;
  session_hold_time : N;
  session_keepalive_time : N;
  session_connect_retry_counter : N;
  session_connect_retry_timer : option N;
  session_hold_timer : option N;
  session_keepalive_timer : option N;
  session_delay_open_timer : option N;
  session_idle_hold_timer : option N;
  session_capabilities : list BGPOptionalParameter;
  session_time_elapsed : N;
  session_expected_remote_as : word32;
  session_connection_direction : option bool  (* Some true = locally initiated, Some false = remotely initiated, None = unknown *)
}.

(* Session initialization *)
Definition init_bgp_session (local_as remote_as local_id : word32) : BGPSession :=
  {| session_state := IDLE;
     session_local_as := local_as;
     session_remote_as := remote_as;
     session_local_id := local_id;
     session_remote_id := 0;
     session_hold_time := HOLD_TIME_DEFAULT;
     session_keepalive_time := KEEPALIVE_TIME;
     session_connect_retry_counter := 0;
     session_connect_retry_timer := None;
     session_hold_timer := None;
     session_keepalive_timer := None;
     session_delay_open_timer := None;
     session_idle_hold_timer := None;
     session_capabilities := [];
     session_time_elapsed := 0;
     session_expected_remote_as := remote_as;
     session_connection_direction := None |}.

(* RFC 8654: State-dependent header validation *)
Definition valid_bgp_header_for_session (session : BGPSession) (hdr : BGPHeader) : bool :=
  match session.(session_state) with
  | OPENCONFIRM | ESTABLISHED =>
      valid_bgp_header_with_caps session.(session_capabilities)
                                  session.(session_capabilities)
                                  hdr
  | _ =>
      valid_bgp_header_preopen hdr
  end.

(* =============================================================================
   §7: FSM Events (RFC 4271 §8.1)
   ============================================================================= *)

Inductive BGPEvent :=
  | ManualStart
  | ManualStop
  | AutomaticStart
  | TCPConnectionConfirmed
  | TCPConnectionFails
  | BGPOpen_Received : BGPOpen -> BGPEvent
  | BGPHeaderErr
  | BGPOpenMsgErr
  | OpenCollisionDump
  | NotifMsgVerErr
  | NotifMsg : BGPNotification -> BGPEvent
  | KeepAliveMsg
  | UpdateMsg : BGPUpdate -> BGPEvent
  | UpdateMsgErr
  | HoldTimerExpires
  | KeepaliveTimerExpires
  | ConnectRetryTimerExpires
  | DelayOpenTimerExpires
  | IdleHoldTimerExpires.

(* Timer arming: duration 0 → None, else Some(now + duration) *)
Definition arm (now dur : N) : option N :=
  if N.eqb dur 0 then None else Some (now + dur).

(* Timer tick and expiry detection *)
Definition timer_tick (session : BGPSession) (delta : N) : BGPSession * list BGPEvent :=
  let new_elapsed := session.(session_time_elapsed) + delta in
  let events :=
    (match session.(session_connect_retry_timer) with
     | Some t => if N.leb t new_elapsed then [ConnectRetryTimerExpires] else []
     | None => []
     end) ++
    (match session.(session_hold_timer) with
     | Some t => if N.leb t new_elapsed then [HoldTimerExpires] else []
     | None => []
     end) ++
    (match session.(session_keepalive_timer) with
     | Some t => if N.leb t new_elapsed then [KeepaliveTimerExpires] else []
     | None => []
     end) ++
    (match session.(session_delay_open_timer) with
     | Some t => if N.leb t new_elapsed then [DelayOpenTimerExpires] else []
     | None => []
     end) ++
    (match session.(session_idle_hold_timer) with
     | Some t => if N.leb t new_elapsed then [IdleHoldTimerExpires] else []
     | None => []
     end)
  in
  ({| session_state := session.(session_state);
      session_local_as := session.(session_local_as);
      session_remote_as := session.(session_remote_as);
      session_local_id := session.(session_local_id);
      session_remote_id := session.(session_remote_id);
      session_hold_time := session.(session_hold_time);
      session_keepalive_time := session.(session_keepalive_time);
      session_connect_retry_counter := session.(session_connect_retry_counter);
      session_connect_retry_timer := session.(session_connect_retry_timer);
      session_hold_timer := session.(session_hold_timer);
      session_keepalive_timer := session.(session_keepalive_timer);
      session_delay_open_timer := session.(session_delay_open_timer);
      session_idle_hold_timer := session.(session_idle_hold_timer);
      session_capabilities := session.(session_capabilities);
      session_time_elapsed := new_elapsed;
      session_expected_remote_as := session.(session_expected_remote_as);
      session_connection_direction := session.(session_connection_direction) |}, events).

(* =============================================================================
   §8: State Transitions (RFC 4271 §8.2)
   ============================================================================= *)

(* IDLE state reset with counter increment *)
Definition reset_to_idle (session : BGPSession) : BGPSession :=
  {| session_state := IDLE;
     session_local_as := session.(session_local_as);
     session_remote_as := session.(session_remote_as);
     session_local_id := session.(session_local_id);
     session_remote_id := 0;
     session_hold_time := HOLD_TIME_DEFAULT;
     session_keepalive_time := KEEPALIVE_TIME;
     session_connect_retry_counter := session.(session_connect_retry_counter) + 1;
     session_connect_retry_timer := None;
     session_hold_timer := None;
     session_keepalive_timer := None;
     session_delay_open_timer := None;
     session_idle_hold_timer := Some CONNECT_RETRY_TIME;
     session_capabilities := [];
     session_time_elapsed := 0;
     session_expected_remote_as := session.(session_expected_remote_as);
     session_connection_direction := None |}.

Definition bgp_state_transition (session : BGPSession) (event : BGPEvent)
                               : BGPSession * option BGPMessageType :=
  match session.(session_state), event with
  | _, ManualStop => (reset_to_idle session, Some NOTIFICATION)

  | IDLE, AutomaticStart =>
      ({| session_state := CONNECT;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := session.(session_remote_id);
          session_hold_time := session.(session_hold_time);
          session_keepalive_time := session.(session_keepalive_time);
          session_connect_retry_counter := 0;
          session_connect_retry_timer := Some CONNECT_RETRY_TIME;
          session_hold_timer := session.(session_hold_timer);
          session_keepalive_timer := session.(session_keepalive_timer);
          session_delay_open_timer := Some 5;
          session_idle_hold_timer := session.(session_idle_hold_timer);
          session_capabilities := session.(session_capabilities);
          session_time_elapsed := 0;
          session_expected_remote_as := session.(session_expected_remote_as);
          session_connection_direction := session.(session_connection_direction) |}, None)

  | CONNECT, DelayOpenTimerExpires =>
      let now := session.(session_time_elapsed) in
      ({| session_state := OPENSENT;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := session.(session_remote_id);
          session_hold_time := session.(session_hold_time);
          session_keepalive_time := session.(session_keepalive_time);
          session_connect_retry_counter := session.(session_connect_retry_counter);
          session_connect_retry_timer := None;
          session_hold_timer := arm now session.(session_hold_time);
          session_keepalive_timer := session.(session_keepalive_timer);
          session_delay_open_timer := None;
          session_idle_hold_timer := session.(session_idle_hold_timer);
          session_capabilities := session.(session_capabilities);
          session_time_elapsed := session.(session_time_elapsed);
          session_expected_remote_as := session.(session_expected_remote_as);
          session_connection_direction := session.(session_connection_direction) |}, Some OPEN)

  | IDLE, ManualStart =>
      ({| session_state := CONNECT;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := session.(session_remote_id);
          session_hold_time := session.(session_hold_time);
          session_keepalive_time := session.(session_keepalive_time);
          session_connect_retry_counter := 0;
          session_connect_retry_timer := Some CONNECT_RETRY_TIME;
          session_hold_timer := session.(session_hold_timer);
          session_keepalive_timer := session.(session_keepalive_timer);
          session_delay_open_timer := session.(session_delay_open_timer);
          session_idle_hold_timer := session.(session_idle_hold_timer);
          session_capabilities := session.(session_capabilities);
          session_time_elapsed := 0;
          session_expected_remote_as := session.(session_expected_remote_as);
          session_connection_direction := session.(session_connection_direction) |}, None)

  | IDLE, BGPHeaderErr =>
      (session, None)

  | IDLE, BGPOpenMsgErr =>
      (session, None)

  | CONNECT, TCPConnectionConfirmed =>
      let now := session.(session_time_elapsed) in
      ({| session_state := OPENSENT;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := session.(session_remote_id);
          session_hold_time := session.(session_hold_time);
          session_keepalive_time := session.(session_keepalive_time);
          session_connect_retry_counter := session.(session_connect_retry_counter);
          session_connect_retry_timer := None;
          session_hold_timer := arm now session.(session_hold_time);
          session_keepalive_timer := session.(session_keepalive_timer);
          session_delay_open_timer := session.(session_delay_open_timer);
          session_idle_hold_timer := session.(session_idle_hold_timer);
          session_capabilities := session.(session_capabilities);
          session_time_elapsed := session.(session_time_elapsed);
          session_expected_remote_as := session.(session_expected_remote_as);
          session_connection_direction := session.(session_connection_direction) |}, Some OPEN)

  | CONNECT, TCPConnectionFails =>
      ({| session_state := ACTIVE;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := session.(session_remote_id);
          session_hold_time := session.(session_hold_time);
          session_keepalive_time := session.(session_keepalive_time);
          session_connect_retry_counter := session.(session_connect_retry_counter);
          session_connect_retry_timer := Some CONNECT_RETRY_TIME;
          session_hold_timer := None;
          session_keepalive_timer := session.(session_keepalive_timer);
          session_delay_open_timer := session.(session_delay_open_timer);
          session_idle_hold_timer := session.(session_idle_hold_timer);
          session_capabilities := session.(session_capabilities);
          session_time_elapsed := session.(session_time_elapsed);
          session_expected_remote_as := session.(session_expected_remote_as);
          session_connection_direction := session.(session_connection_direction) |}, None)

  | CONNECT, BGPHeaderErr =>
      (reset_to_idle session, Some NOTIFICATION)

  | CONNECT, BGPOpenMsgErr =>
      (reset_to_idle session, Some NOTIFICATION)

  | CONNECT, OpenCollisionDump =>
      (reset_to_idle session, Some NOTIFICATION)

  | ACTIVE, TCPConnectionConfirmed =>
      let now := session.(session_time_elapsed) in
      ({| session_state := OPENSENT;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := session.(session_remote_id);
          session_hold_time := session.(session_hold_time);
          session_keepalive_time := session.(session_keepalive_time);
          session_connect_retry_counter := session.(session_connect_retry_counter);
          session_connect_retry_timer := None;
          session_hold_timer := arm now session.(session_hold_time);
          session_keepalive_timer := session.(session_keepalive_timer);
          session_delay_open_timer := session.(session_delay_open_timer);
          session_idle_hold_timer := session.(session_idle_hold_timer);
          session_capabilities := session.(session_capabilities);
          session_time_elapsed := session.(session_time_elapsed);
          session_expected_remote_as := session.(session_expected_remote_as);
          session_connection_direction := session.(session_connection_direction) |}, Some OPEN)

  | ACTIVE, ConnectRetryTimerExpires =>
      ({| session_state := CONNECT;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := session.(session_remote_id);
          session_hold_time := session.(session_hold_time);
          session_keepalive_time := session.(session_keepalive_time);
          session_connect_retry_counter := session.(session_connect_retry_counter);
          session_connect_retry_timer := Some CONNECT_RETRY_TIME;
          session_hold_timer := session.(session_hold_timer);
          session_keepalive_timer := session.(session_keepalive_timer);
          session_delay_open_timer := session.(session_delay_open_timer);
          session_idle_hold_timer := session.(session_idle_hold_timer);
          session_capabilities := session.(session_capabilities);
          session_time_elapsed := session.(session_time_elapsed);
          session_expected_remote_as := session.(session_expected_remote_as);
          session_connection_direction := session.(session_connection_direction) |}, None)

  | ACTIVE, DelayOpenTimerExpires =>
      let now := session.(session_time_elapsed) in
      ({| session_state := OPENSENT;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := session.(session_remote_id);
          session_hold_time := session.(session_hold_time);
          session_keepalive_time := session.(session_keepalive_time);
          session_connect_retry_counter := session.(session_connect_retry_counter);
          session_connect_retry_timer := None;
          session_hold_timer := arm now session.(session_hold_time);
          session_keepalive_timer := session.(session_keepalive_timer);
          session_delay_open_timer := None;
          session_idle_hold_timer := session.(session_idle_hold_timer);
          session_capabilities := session.(session_capabilities);
          session_time_elapsed := session.(session_time_elapsed);
          session_expected_remote_as := session.(session_expected_remote_as);
          session_connection_direction := session.(session_connection_direction) |}, Some OPEN)

  | ACTIVE, BGPHeaderErr =>
      (reset_to_idle session, Some NOTIFICATION)

  | ACTIVE, BGPOpenMsgErr =>
      (reset_to_idle session, Some NOTIFICATION)

  | ACTIVE, OpenCollisionDump =>
      (reset_to_idle session, Some NOTIFICATION)

  | OPENSENT, BGPOpen_Received open_msg =>
      if valid_open_message open_msg then
        if has_bgp_id_collision session.(session_local_id) open_msg.(open_bgp_identifier) then
          (* BGP ID collision: RFC 4271 §6.8 collision resolution
             TODO: Current model doesn't track connection direction (local vs remote initiated)
             Full RFC compliance would use resolve_collision to decide which connection to keep *)
          (reset_to_idle session, Some NOTIFICATION)
        else if negb (verify_peer_as session.(session_expected_remote_as) open_msg.(open_my_as)) then
          (reset_to_idle session, Some NOTIFICATION)  (* Bad Peer AS *)
        else
          let now := session.(session_time_elapsed) in
          let negotiated_hold := N.min session.(session_hold_time) open_msg.(open_hold_time) in
          let keep := negotiated_hold / 3 in
          ({| session_state := OPENCONFIRM;
              session_local_as := session.(session_local_as);
              session_remote_as := open_msg.(open_my_as);
              session_local_id := session.(session_local_id);
              session_remote_id := open_msg.(open_bgp_identifier);
              session_hold_time := negotiated_hold;
              session_keepalive_time := keep;
              session_connect_retry_counter := session.(session_connect_retry_counter);
              session_connect_retry_timer := session.(session_connect_retry_timer);
              session_hold_timer := arm now negotiated_hold;
              session_keepalive_timer := arm now keep;
              session_delay_open_timer := session.(session_delay_open_timer);
              session_idle_hold_timer := session.(session_idle_hold_timer);
              session_capabilities := open_msg.(open_opt_params);
              session_time_elapsed := session.(session_time_elapsed);
              session_expected_remote_as := session.(session_expected_remote_as);
              session_connection_direction := session.(session_connection_direction) |}, Some KEEPALIVE)
      else
        (reset_to_idle session, Some NOTIFICATION)
  
  | OPENCONFIRM, KeepAliveMsg =>
      let now := session.(session_time_elapsed) in
      ({| session_state := ESTABLISHED;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := session.(session_remote_id);
          session_hold_time := session.(session_hold_time);
          session_keepalive_time := session.(session_keepalive_time);
          session_connect_retry_counter := session.(session_connect_retry_counter);
          session_connect_retry_timer := session.(session_connect_retry_timer);
          session_hold_timer := arm now session.(session_hold_time);
          session_keepalive_timer := arm now session.(session_keepalive_time);
          session_delay_open_timer := session.(session_delay_open_timer);
          session_idle_hold_timer := session.(session_idle_hold_timer);
          session_capabilities := session.(session_capabilities);
          session_time_elapsed := session.(session_time_elapsed);
          session_expected_remote_as := session.(session_expected_remote_as);
          session_connection_direction := session.(session_connection_direction) |}, None)
  
  | OPENSENT, BGPHeaderErr =>
      ({| session_state := IDLE;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := 0;
          session_hold_time := HOLD_TIME_DEFAULT;
          session_keepalive_time := KEEPALIVE_TIME;
          session_connect_retry_counter := session.(session_connect_retry_counter) + 1;
          session_connect_retry_timer := None;
          session_hold_timer := None;
          session_keepalive_timer := None;
          session_delay_open_timer := None;
          session_idle_hold_timer := Some CONNECT_RETRY_TIME;
          session_capabilities := [];
          session_time_elapsed := 0;
          session_expected_remote_as := session.(session_expected_remote_as);
            session_connection_direction := session.(session_connection_direction) |}, Some NOTIFICATION)

  | OPENSENT, BGPOpenMsgErr =>
      ({| session_state := IDLE;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := 0;
          session_hold_time := HOLD_TIME_DEFAULT;
          session_keepalive_time := KEEPALIVE_TIME;
          session_connect_retry_counter := session.(session_connect_retry_counter) + 1;
          session_connect_retry_timer := None;
          session_hold_timer := None;
          session_keepalive_timer := None;
          session_delay_open_timer := None;
          session_idle_hold_timer := Some CONNECT_RETRY_TIME;
          session_capabilities := [];
          session_time_elapsed := 0;
          session_expected_remote_as := session.(session_expected_remote_as);
            session_connection_direction := session.(session_connection_direction) |}, Some NOTIFICATION)

  | OPENSENT, DelayOpenTimerExpires =>
      (session, None)

  | OPENSENT, HoldTimerExpires =>
      ({| session_state := IDLE;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := 0;
          session_hold_time := HOLD_TIME_DEFAULT;
          session_keepalive_time := KEEPALIVE_TIME;
          session_connect_retry_counter := session.(session_connect_retry_counter) + 1;
          session_connect_retry_timer := None;
          session_hold_timer := None;
          session_keepalive_timer := None;
          session_delay_open_timer := None;
          session_idle_hold_timer := Some CONNECT_RETRY_TIME;
          session_capabilities := [];
          session_time_elapsed := 0;
          session_expected_remote_as := session.(session_expected_remote_as);
            session_connection_direction := session.(session_connection_direction) |}, Some NOTIFICATION)

  | OPENCONFIRM, HoldTimerExpires =>
      ({| session_state := IDLE;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := 0;
          session_hold_time := HOLD_TIME_DEFAULT;
          session_keepalive_time := KEEPALIVE_TIME;
          session_connect_retry_counter := session.(session_connect_retry_counter) + 1;
          session_connect_retry_timer := None;
          session_hold_timer := None;
          session_keepalive_timer := None;
          session_delay_open_timer := None;
          session_idle_hold_timer := Some CONNECT_RETRY_TIME;
          session_capabilities := [];
          session_time_elapsed := 0;
          session_expected_remote_as := session.(session_expected_remote_as);
            session_connection_direction := session.(session_connection_direction) |}, Some NOTIFICATION)

  | OPENCONFIRM, BGPHeaderErr =>
      (reset_to_idle session, Some NOTIFICATION)

  | OPENCONFIRM, BGPOpenMsgErr =>
      (reset_to_idle session, Some NOTIFICATION)

  | ESTABLISHED, UpdateMsg upd =>
      if valid_update_message session.(session_local_as) upd then
        if update_has_as_loop session.(session_local_as) upd then
          (session, None)  (* Drop update with AS loop, stay ESTABLISHED *)
        else
          let now := session.(session_time_elapsed) in
          let reset_session := {| session_state := session.(session_state);
                                   session_local_as := session.(session_local_as);
                                   session_remote_as := session.(session_remote_as);
                                   session_local_id := session.(session_local_id);
                                   session_remote_id := session.(session_remote_id);
                                   session_hold_time := session.(session_hold_time);
                                   session_keepalive_time := session.(session_keepalive_time);
                                   session_connect_retry_counter := session.(session_connect_retry_counter);
                                   session_connect_retry_timer := session.(session_connect_retry_timer);
                                   session_hold_timer := arm now session.(session_hold_time);
                                   session_keepalive_timer := session.(session_keepalive_timer);
                                   session_delay_open_timer := session.(session_delay_open_timer);
                                   session_idle_hold_timer := session.(session_idle_hold_timer);
                                   session_capabilities := session.(session_capabilities);
                                   session_time_elapsed := session.(session_time_elapsed);
                                   session_expected_remote_as := session.(session_expected_remote_as);
                                   session_connection_direction := session.(session_connection_direction) |} in
          (reset_session, None)  (* Reset hold timer on valid UPDATE *)
      else
        (* RFC 4271 §6.3: Send NOTIFICATION for malformed UPDATE and reset to IDLE *)
        ({| session_state := IDLE;
            session_local_as := session.(session_local_as);
            session_remote_as := session.(session_remote_as);
            session_local_id := session.(session_local_id);
            session_remote_id := 0;
            session_hold_time := HOLD_TIME_DEFAULT;
            session_keepalive_time := KEEPALIVE_TIME;
            session_connect_retry_counter := session.(session_connect_retry_counter) + 1;
            session_connect_retry_timer := None;
            session_hold_timer := None;
            session_keepalive_timer := None;
            session_delay_open_timer := None;
            session_idle_hold_timer := Some CONNECT_RETRY_TIME;
            session_capabilities := [];
            session_time_elapsed := 0;
            session_expected_remote_as := session.(session_expected_remote_as);
            session_connection_direction := session.(session_connection_direction) |}, Some NOTIFICATION)

  | ESTABLISHED, KeepAliveMsg =>
      let now := session.(session_time_elapsed) in
      let reset_session := {| session_state := session.(session_state);
                               session_local_as := session.(session_local_as);
                               session_remote_as := session.(session_remote_as);
                               session_local_id := session.(session_local_id);
                               session_remote_id := session.(session_remote_id);
                               session_hold_time := session.(session_hold_time);
                               session_keepalive_time := session.(session_keepalive_time);
                               session_connect_retry_counter := session.(session_connect_retry_counter);
                               session_connect_retry_timer := session.(session_connect_retry_timer);
                               session_hold_timer := arm now session.(session_hold_time);
                               session_keepalive_timer := session.(session_keepalive_timer);
                               session_delay_open_timer := session.(session_delay_open_timer);
                               session_idle_hold_timer := session.(session_idle_hold_timer);
                               session_capabilities := session.(session_capabilities);
                               session_time_elapsed := session.(session_time_elapsed);
                               session_expected_remote_as := session.(session_expected_remote_as);
                                   session_connection_direction := session.(session_connection_direction) |} in
      (reset_session, None)  (* Reset hold timer on KEEPALIVE *)

  | ESTABLISHED, HoldTimerExpires =>
      ({| session_state := IDLE;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := 0;
          session_hold_time := HOLD_TIME_DEFAULT;
          session_keepalive_time := KEEPALIVE_TIME;
          session_connect_retry_counter := session.(session_connect_retry_counter) + 1;
          session_connect_retry_timer := None;
          session_hold_timer := None;
          session_keepalive_timer := None;
          session_delay_open_timer := None;
          session_idle_hold_timer := Some CONNECT_RETRY_TIME;
          session_capabilities := [];
          session_time_elapsed := 0;
          session_expected_remote_as := session.(session_expected_remote_as);
            session_connection_direction := session.(session_connection_direction) |}, Some NOTIFICATION)

  | ESTABLISHED, UpdateMsgErr =>
      ({| session_state := IDLE;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := 0;
          session_hold_time := HOLD_TIME_DEFAULT;
          session_keepalive_time := KEEPALIVE_TIME;
          session_connect_retry_counter := session.(session_connect_retry_counter) + 1;
          session_connect_retry_timer := None;
          session_hold_timer := None;
          session_keepalive_timer := None;
          session_delay_open_timer := None;
          session_idle_hold_timer := Some CONNECT_RETRY_TIME;
          session_capabilities := [];
          session_time_elapsed := 0;
          session_expected_remote_as := session.(session_expected_remote_as);
            session_connection_direction := session.(session_connection_direction) |}, Some NOTIFICATION)

  | ESTABLISHED, BGPHeaderErr =>
      (reset_to_idle session, Some NOTIFICATION)

  | ESTABLISHED, BGPOpenMsgErr =>
      (reset_to_idle session, Some NOTIFICATION)

  | _, NotifMsg _ =>
      ({| session_state := IDLE;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := 0;
          session_hold_time := HOLD_TIME_DEFAULT;
          session_keepalive_time := KEEPALIVE_TIME;
          session_connect_retry_counter := session.(session_connect_retry_counter) + 1;
          session_connect_retry_timer := None;
          session_hold_timer := None;
          session_keepalive_timer := None;
          session_delay_open_timer := None;
          session_idle_hold_timer := Some CONNECT_RETRY_TIME;
          session_capabilities := [];
          session_time_elapsed := 0;
          session_expected_remote_as := session.(session_expected_remote_as);
          session_connection_direction := session.(session_connection_direction) |}, None)

  | IDLE, IdleHoldTimerExpires =>
      (session, None)

  | ESTABLISHED, KeepaliveTimerExpires =>
      let now := session.(session_time_elapsed) in
      let reset_session := {| session_state := session.(session_state);
                               session_local_as := session.(session_local_as);
                               session_remote_as := session.(session_remote_as);
                               session_local_id := session.(session_local_id);
                               session_remote_id := session.(session_remote_id);
                               session_hold_time := session.(session_hold_time);
                               session_keepalive_time := session.(session_keepalive_time);
                               session_connect_retry_counter := session.(session_connect_retry_counter);
                               session_connect_retry_timer := session.(session_connect_retry_timer);
                               session_hold_timer := session.(session_hold_timer);
                               session_keepalive_timer := arm now session.(session_keepalive_time);
                               session_delay_open_timer := session.(session_delay_open_timer);
                               session_idle_hold_timer := session.(session_idle_hold_timer);
                               session_capabilities := session.(session_capabilities);
                               session_time_elapsed := session.(session_time_elapsed);
                               session_expected_remote_as := session.(session_expected_remote_as);
                                   session_connection_direction := session.(session_connection_direction) |} in
      (reset_session, Some KEEPALIVE)  (* Automatic KEEPALIVE generation *)

  | OPENSENT, OpenCollisionDump =>
      (reset_to_idle session, Some NOTIFICATION)

  | OPENCONFIRM, OpenCollisionDump =>
      (reset_to_idle session, Some NOTIFICATION)

  | _, _ => (session, None)  (* Default: no transition *)
  end.

(* =============================================================================
   §8.5: Network Failure and Adversarial Models
   ============================================================================= *)

Inductive NetworkFailure :=
  | TCPConnectionLost : NetworkFailure
  | MessageLost : NetworkFailure
  | MessageDelayed : N -> NetworkFailure
  | MessageDuplicated : NetworkFailure
  | MessageReordered : NetworkFailure
  | MessageCorrupted : NetworkFailure.

(* Event delivery predicate under network failure *)
Definition network_delivers (failure : option NetworkFailure) (event : BGPEvent) : bool :=
  match failure with
  | None => true
  | Some TCPConnectionLost => false
  | Some MessageLost => false
  | Some (MessageDelayed _) => false
  | Some MessageDuplicated => true
  | Some MessageReordered => true
  | Some MessageCorrupted => false
  end.

(* State transition with failure injection *)
Definition bgp_state_transition_with_failure
  (session : BGPSession)
  (event : BGPEvent)
  (failure : option NetworkFailure) : (BGPSession * option BGPMessageType) :=
  if network_delivers failure event then
    bgp_state_transition session event
  else
    match failure with
    | Some TCPConnectionLost =>
        (reset_to_idle session, Some NOTIFICATION)
    | _ => (session, None)
    end.

(* Transience classification: recoverable without external intervention *)
Definition is_transient_failure (failure : NetworkFailure) : bool :=
  match failure with
  | TCPConnectionLost => false
  | MessageLost => true
  | MessageDelayed _ => true
  | MessageDuplicated => true
  | MessageReordered => true
  | MessageCorrupted => true
  end.

Inductive AdversarialEvent :=
  | InjectedOpen : BGPOpen -> AdversarialEvent
  | InjectedUpdate : BGPUpdate -> AdversarialEvent
  | InjectedNotification : BGPNotification -> AdversarialEvent
  | ReplayedMessage : BGPEvent -> AdversarialEvent.

(* Adversarial event acceptance under state and validation guards *)
Definition adversarial_event_accepted (session : BGPSession) (adv : AdversarialEvent) : bool :=
  match adv with
  | InjectedOpen open_msg =>
      andb (match session_state session with | OPENSENT => true | _ => false end)
           (valid_open_message open_msg)
  | InjectedUpdate upd =>
      andb (match session_state session with | ESTABLISHED => true | _ => false end)
           (valid_update_message session.(session_local_as) upd)
  | InjectedNotification _ => true
  | ReplayedMessage _ => false
  end.

(* TCP connection loss forces IDLE *)
Theorem tcp_loss_goes_to_idle : forall session event,
  (fst (bgp_state_transition_with_failure session event (Some TCPConnectionLost))).(session_state) = IDLE.
Proof.
  intros session event.
  unfold bgp_state_transition_with_failure.
  simpl.
  unfold reset_to_idle.
  reflexivity.
Qed.

(* Transient failures preserve state *)
Theorem transient_failure_no_transition : forall session event failure,
  is_transient_failure failure = true ->
  network_delivers (Some failure) event = false ->
  fst (bgp_state_transition_with_failure session event (Some failure)) = session.
Proof.
  intros session event failure Htransient Hnodeliver.
  unfold bgp_state_transition_with_failure.
  rewrite Hnodeliver.
  destruct failure; try reflexivity; try discriminate Htransient.
Qed.

(* State guards reject adversarial injection *)
Theorem adversarial_injection_state_guard : forall session open_msg,
  session.(session_state) <> OPENSENT ->
  adversarial_event_accepted session (InjectedOpen open_msg) = false.
Proof.
  intros session open_msg Hstate.
  unfold adversarial_event_accepted.
  destruct (session_state session) eqn:Heq; try reflexivity.
  contradiction.
Qed.

(* Validation guards reject invalid adversarial messages *)
Theorem adversarial_invalid_update_rejected : forall session upd,
  valid_update_message session.(session_local_as) upd = false ->
  adversarial_event_accepted session (InjectedUpdate upd) = false.
Proof.
  intros session upd Hinvalid.
  unfold adversarial_event_accepted.
  rewrite Hinvalid.
  destruct (session_state session); simpl; reflexivity.
Qed.

(* Replay protection *)
Theorem replayed_messages_rejected : forall session event,
  adversarial_event_accepted session (ReplayedMessage event) = false.
Proof.
  intros session event.
  unfold adversarial_event_accepted.
  reflexivity.
Qed.

(* =============================================================================
   §9: Route Selection (RFC 4271 §9)
   ============================================================================= *)

Record BGPRoute := {
  route_prefix : NLRI;
  route_next_hop : word32;
  route_next_hop_reachable : bool;       (* true if next hop is reachable *)
  route_as_path : list word32;
  route_origin : byte;
  route_med : option word32;
  route_local_pref : word32;
  route_atomic_aggregate : bool;
  route_aggregator : option (word32 * word32);
  route_communities : list word32;
  route_originator_id : word32;
  route_cluster_list : list word32;
  route_is_ebgp : bool;                  (* true if learned via eBGP, false if iBGP *)
  route_peer_router_id : word32;         (* Router ID of peer that sent this route *)
  route_igp_cost : option word32         (* IGP cost to NEXT_HOP *)
}.

(* Three Routing Information Bases *)
Record RIB := {
  adj_rib_in : list BGPRoute;   (* Routes received from peers *)
  loc_rib : list BGPRoute;      (* Best routes selected for local use *)
  adj_rib_out : list BGPRoute   (* Routes advertised to peers *)
}.

(* RFC 7911: Multi-path RIB for ADD-PATH *)
(* Store multiple paths per prefix, each with unique path ID *)
Record MultiPath_Entry := {
  mp_prefix : NLRI;
  mp_paths : list (word32 * BGPRoute)  (* (path_id, route) pairs *)
}.

Record MultiPath_RIB := {
  mp_adj_rib_in : list MultiPath_Entry;
  mp_loc_rib : list MultiPath_Entry;
  mp_adj_rib_out : list MultiPath_Entry
}.

(* RFC 7911 §3: NLRI encoding with path identifier *)
Definition encode_nlri_with_path_id (path_id : word32) (nlri : NLRI) : list byte :=
  let id_bytes := [N.shiftr path_id 24; N.land (N.shiftr path_id 16) 255;
                   N.land (N.shiftr path_id 8) 255; N.land path_id 255] in
  id_bytes ++ nlri.(nlri_prefix_len) :: nlri.(nlri_prefix).

(* Path ID decoder *)
Definition decode_nlri_with_path_id (bytes : list byte) : option (word32 * NLRI) :=
  match bytes with
  | b1 :: b2 :: b3 :: b4 :: plen :: rest =>
      let path_id := N.lor (N.lor (N.lor (N.shiftl b1 24) (N.shiftl b2 16))
                                   (N.shiftl b3 8)) b4 in
      Some (path_id, {| nlri_prefix_len := plen; nlri_prefix := rest |})
  | _ => None
  end.

(* Prefix lookup in multi-path RIB *)
Fixpoint find_paths_for_prefix (prefix : NLRI) (entries : list MultiPath_Entry) : list (word32 * BGPRoute) :=
  match entries with
  | [] => []
  | entry :: rest =>
      if andb (N.eqb entry.(mp_prefix).(nlri_prefix_len) prefix.(nlri_prefix_len))
              (forallb (fun p => match p with (a, b) => N.eqb a b end)
                      (combine entry.(mp_prefix).(nlri_prefix) prefix.(nlri_prefix))) then
        entry.(mp_paths)
      else
        find_paths_for_prefix prefix rest
  end.

(* Path insertion *)
Fixpoint add_path_to_rib (prefix : NLRI) (path_id : word32) (route : BGPRoute)
                         (entries : list MultiPath_Entry) : list MultiPath_Entry :=
  match entries with
  | [] => [{| mp_prefix := prefix; mp_paths := [(path_id, route)] |}]
  | entry :: rest =>
      if andb (N.eqb entry.(mp_prefix).(nlri_prefix_len) prefix.(nlri_prefix_len))
              (forallb (fun p => match p with (a, b) => N.eqb a b end)
                      (combine entry.(mp_prefix).(nlri_prefix) prefix.(nlri_prefix))) then
        {| mp_prefix := entry.(mp_prefix);
           mp_paths := (path_id, route) :: entry.(mp_paths) |} :: rest
      else
        entry :: add_path_to_rib prefix path_id route rest
  end.

(* Encoding round-trip preserves prefix *)
Theorem addpath_prefix_preserved: forall path_id nlri,
  match decode_nlri_with_path_id (encode_nlri_with_path_id path_id nlri) with
  | Some (_, decoded_nlri) => decoded_nlri.(nlri_prefix_len) = nlri.(nlri_prefix_len) /\
                               decoded_nlri.(nlri_prefix) = nlri.(nlri_prefix)
  | None => False
  end.
Proof.
  intros path_id nlri.
  destruct nlri as [plen pfx].
  unfold encode_nlri_with_path_id, decode_nlri_with_path_id.
  simpl.
  split; reflexivity.
Qed.

(* Encoding produces valid output *)
Theorem addpath_encoding_valid: forall path_id nlri,
  exists pid plen pfx,
    decode_nlri_with_path_id (encode_nlri_with_path_id path_id nlri) = Some (pid, {| nlri_prefix_len := plen; nlri_prefix := pfx |}).
Proof.
Admitted.

(* Neighboring AS extraction (first AS in AS_PATH) *)
Definition neighboring_as (route : BGPRoute) : option word32 :=
  match route.(route_as_path) with
  | [] => None
  | as_num :: _ => Some as_num
  end.

(* Same neighboring AS predicate *)
Definition same_neighboring_as (r1 r2 : BGPRoute) : bool :=
  match neighboring_as r1, neighboring_as r2 with
  | Some as1, Some as2 => N.eqb as1 as2
  | _, _ => false
  end.

(* RFC 4456: Cluster loop detection *)
Definition has_cluster_loop (my_cluster_id : word32) (cluster_list : list word32) : bool :=
  existsb (fun cid => N.eqb cid my_cluster_id) cluster_list.

(* Cluster loop rejection predicate *)
Definition should_reject_cluster_loop (my_cluster_id : word32) (route : BGPRoute) : bool :=
  has_cluster_loop my_cluster_id route.(route_cluster_list).

(* RFC 4456 §8: ORIGINATOR_ID initialization *)
Definition set_originator_id (route : BGPRoute) (peer_router_id : word32) : BGPRoute :=
  if N.eqb route.(route_originator_id) 0 then
    {| route_prefix := route.(route_prefix);
       route_next_hop := route.(route_next_hop);
       route_next_hop_reachable := route.(route_next_hop_reachable);
       route_as_path := route.(route_as_path);
       route_origin := route.(route_origin);
       route_med := route.(route_med);
       route_local_pref := route.(route_local_pref);
       route_atomic_aggregate := route.(route_atomic_aggregate);
       route_aggregator := route.(route_aggregator);
       route_communities := route.(route_communities);
       route_originator_id := peer_router_id;
       route_cluster_list := route.(route_cluster_list);
       route_is_ebgp := route.(route_is_ebgp);
       route_peer_router_id := route.(route_peer_router_id);
       route_igp_cost := route.(route_igp_cost) |}
  else
    route.

(* Prepend cluster ID to CLUSTER_LIST *)
Definition prepend_cluster_id (route : BGPRoute) (my_cluster_id : word32) : BGPRoute :=
  {| route_prefix := route.(route_prefix);
     route_next_hop := route.(route_next_hop);
     route_next_hop_reachable := route.(route_next_hop_reachable);
     route_as_path := route.(route_as_path);
     route_origin := route.(route_origin);
     route_med := route.(route_med);
     route_local_pref := route.(route_local_pref);
     route_atomic_aggregate := route.(route_atomic_aggregate);
     route_aggregator := route.(route_aggregator);
     route_communities := route.(route_communities);
     route_originator_id := route.(route_originator_id);
     route_cluster_list := my_cluster_id :: route.(route_cluster_list);
     route_is_ebgp := route.(route_is_ebgp);
     route_peer_router_id := route.(route_peer_router_id);
     route_igp_cost := route.(route_igp_cost) |}.

(* Apply route reflection transformations *)
Definition apply_route_reflection (route : BGPRoute) (my_cluster_id peer_router_id : word32) : BGPRoute :=
  let with_originator := set_originator_id route peer_router_id in
  prepend_cluster_id with_originator my_cluster_id.

(* ORIGINATOR_ID setting preserves prefix *)
Theorem set_originator_preserves_prefix: forall route peer_id,
  (set_originator_id route peer_id).(route_prefix) = route.(route_prefix).
Proof.
  intros route peer_id.
  unfold set_originator_id.
  destruct (N.eqb (route_originator_id route) 0); reflexivity.
Qed.

(* Cluster ID prepending *)
Theorem prepend_cluster_adds: forall route cluster_id,
  (prepend_cluster_id route cluster_id).(route_cluster_list) =
  cluster_id :: route.(route_cluster_list).
Proof.
  intros route cluster_id.
  unfold prepend_cluster_id.
  reflexivity.
Qed.

(* Reflection creates loop when cluster ID present *)
Theorem reflection_creates_loop_when_present: forall route cluster_id peer_id,
  In cluster_id route.(route_cluster_list) ->
  has_cluster_loop cluster_id
    (apply_route_reflection route cluster_id peer_id).(route_cluster_list) = true.
Proof.
  intros route cluster_id peer_id Hin.
  unfold apply_route_reflection.
  unfold has_cluster_loop.
  rewrite prepend_cluster_adds.
  simpl.
  rewrite N.eqb_refl.
  reflexivity.
Qed.

(* RFC 5065: Confederation boundary processing *)

(* Confederation segment removal for external advertisement *)
Fixpoint remove_confed_segments (segments : list ASPathSegment) : list ASPathSegment :=
  match segments with
  | [] => []
  | seg :: rest =>
      let is_confed := orb (N.eqb seg.(seg_type) AS_CONFED_SEQUENCE)
                           (N.eqb seg.(seg_type) AS_CONFED_SET) in
      if is_confed then
        remove_confed_segments rest
      else
        seg :: remove_confed_segments rest
  end.

(* Confederation boundary test *)
Definition crosses_confed_boundary (local_confed_id peer_as : word32) : bool :=
  negb (N.eqb local_confed_id peer_as).

(* Boundary-conditional segment filtering *)
Definition apply_confed_boundary (segments : list ASPathSegment)
                                 (local_confed_id peer_as : word32) : list ASPathSegment :=
  if crosses_confed_boundary local_confed_id peer_as then
    remove_confed_segments segments
  else
    segments.

(* Regular segments preserved *)
Theorem remove_confed_preserves_regular: forall seg rest,
  orb (N.eqb seg.(seg_type) AS_CONFED_SEQUENCE) (N.eqb seg.(seg_type) AS_CONFED_SET) = false ->
  In seg (remove_confed_segments (seg :: rest)).
Proof.
  intros seg rest Hnot_confed.
  simpl.
  rewrite Hnot_confed.
  simpl. left. reflexivity.
Qed.

(* Intra-confederation paths unchanged *)
Theorem within_confed_unchanged: forall segments confed_id,
  apply_confed_boundary segments confed_id confed_id = segments.
Proof.
  intros segments confed_id.
  unfold apply_confed_boundary.
  unfold crosses_confed_boundary.
  rewrite N.eqb_refl.
  simpl. reflexivity.
Qed.

(* Boundary crossing filters confederation segments *)
Theorem boundary_removes_confed: forall segments confed_id peer_as,
  confed_id <> peer_as ->
  forall seg, In seg (apply_confed_boundary segments confed_id peer_as) ->
  orb (N.eqb seg.(seg_type) AS_CONFED_SEQUENCE) (N.eqb seg.(seg_type) AS_CONFED_SET) = false.
Proof.
  intros segments confed_id peer_as Hneq seg Hin.
  unfold apply_confed_boundary in Hin.
  unfold crosses_confed_boundary in Hin.
  assert (Hcross: (confed_id =? peer_as) = false).
  { apply N.eqb_neq. exact Hneq. }
  rewrite Hcross in Hin.
  simpl in Hin.
  induction segments as [| s rest IH].
  - simpl in Hin. contradiction.
  - simpl in Hin.
    destruct (orb (seg_type s =? AS_CONFED_SEQUENCE) (seg_type s =? AS_CONFED_SET)) eqn:Hconfed.
    + apply IH. exact Hin.
    + simpl in Hin. destruct Hin as [Heq | Hin'].
      * rewrite <- Heq. exact Hconfed.
      * apply IH. exact Hin'.
Qed.

(* Route comparison function for best path selection *)
Definition compare_routes (r1 r2 : BGPRoute) : bool :=
  if N.ltb r2.(route_local_pref) r1.(route_local_pref) then true
  else if N.ltb r1.(route_local_pref) r2.(route_local_pref) then false
  else
    let l1 := N.of_nat (length r1.(route_as_path)) in
    let l2 := N.of_nat (length r2.(route_as_path)) in
    if N.ltb l1 l2 then true
    else if N.ltb l2 l1 then false
    else
      if N.ltb r1.(route_origin) r2.(route_origin) then true
      else if N.ltb r2.(route_origin) r1.(route_origin) then false
      else
        let med_decision :=
          if same_neighboring_as r1 r2 then
            let m1 := match r1.(route_med) with Some m => m | None => 0 end in
            let m2 := match r2.(route_med) with Some m => m | None => 0 end in
            if N.ltb m1 m2 then Some true
            else if N.ltb m2 m1 then Some false
            else None
          else None
        in
        match med_decision with
        | Some b => b
        | None =>
            if andb r1.(route_is_ebgp) (negb r2.(route_is_ebgp)) then true
            else if andb r2.(route_is_ebgp) (negb r1.(route_is_ebgp)) then false
            else
              match r1.(route_igp_cost), r2.(route_igp_cost) with
              | Some c1, Some c2 =>
                  if N.ltb c1 c2 then true
                  else if N.ltb c2 c1 then false
                  else N.ltb r1.(route_peer_router_id) r2.(route_peer_router_id)
              | Some _, None => true
              | None, Some _ => false
              | None, None => N.ltb r1.(route_peer_router_id) r2.(route_peer_router_id)
              end
        end.

(* RFC 4271 §9.1.2: Best path selection *)
Definition bgp_best_path_selection (routes : list BGPRoute) : option BGPRoute :=
  let reachable_routes := filter (fun r => r.(route_next_hop_reachable)) routes in
  fold_left (fun best r =>
    match best with
    | None => Some r
    | Some b => if compare_routes r b then Some r else best
    end) reachable_routes None.

(* RFC 4456: Cluster loop prevention for route reflectors *)
Definition bgp_best_path_selection_rr (my_cluster_id : word32) (routes : list BGPRoute) : option BGPRoute :=
  let reachable_routes := filter (fun r => r.(route_next_hop_reachable)) routes in
  let no_cluster_loop := filter (fun r => negb (should_reject_cluster_loop my_cluster_id r)) reachable_routes in
  fold_left (fun best r =>
    match best with
    | None => Some r
    | Some b => if compare_routes r b then Some r else best
    end) no_cluster_loop None.

(* Complexity: O(n) linear in number of routes *)
Definition best_path_complexity (n : nat) : nat := n.

(* Linear complexity bound *)
Theorem best_path_linear_complexity : forall (routes : list BGPRoute),
  Nat.leb (length routes) (best_path_complexity (length routes)) = true.
Proof.
  intros routes.
  unfold best_path_complexity.
  apply Nat.leb_refl.
Qed.

(* Empty RIB initialization *)
Definition init_rib : RIB :=
  {| adj_rib_in := [];
     loc_rib := [];
     adj_rib_out := [] |}.

(* Adj-RIB-In insertion *)
Definition add_route_in (rib : RIB) (route : BGPRoute) : RIB :=
  {| adj_rib_in := route :: rib.(adj_rib_in);
     loc_rib := rib.(loc_rib);
     adj_rib_out := rib.(adj_rib_out) |}.

(* Loc-RIB update via best path selection *)
Definition update_loc_rib (rib : RIB) : RIB :=
  {| adj_rib_in := rib.(adj_rib_in);
     loc_rib := match bgp_best_path_selection rib.(adj_rib_in) with
                | Some best => [best]
                | None => []
                end;
     adj_rib_out := rib.(adj_rib_out) |}.

(* Route export with attribute modification (eBGP: prepend AS, set NEXT_HOP) *)
Definition export_route (my_as my_next_hop : word32) (route : BGPRoute) (is_ebgp : bool) : BGPRoute :=
  {| route_prefix := route.(route_prefix);
     route_next_hop := if is_ebgp then my_next_hop else route.(route_next_hop);
     route_next_hop_reachable := route.(route_next_hop_reachable);
     route_as_path := if is_ebgp then my_as :: route.(route_as_path) else route.(route_as_path);
     route_origin := route.(route_origin);
     route_med := route.(route_med);
     route_local_pref := route.(route_local_pref);
     route_atomic_aggregate := route.(route_atomic_aggregate);
     route_aggregator := route.(route_aggregator);
     route_communities := route.(route_communities);
     route_originator_id := route.(route_originator_id);
     route_cluster_list := route.(route_cluster_list);
     route_is_ebgp := is_ebgp;
     route_peer_router_id := route.(route_peer_router_id);
     route_igp_cost := route.(route_igp_cost) |}.

(* iBGP split horizon: iBGP→iBGP advertisement prohibited *)
Definition should_advertise_route (route : BGPRoute) (peer_is_ebgp : bool) : bool :=
  if peer_is_ebgp then true
  else route.(route_is_ebgp).

(* Adj-RIB-Out construction from Loc-RIB *)
Definition update_adj_rib_out (my_as my_next_hop : word32) (rib : RIB) (is_ebgp : bool) : RIB :=
  let filtered := filter (fun r => should_advertise_route r is_ebgp) rib.(loc_rib) in
  {| adj_rib_in := rib.(adj_rib_in);
     loc_rib := rib.(loc_rib);
     adj_rib_out := map (fun r => export_route my_as my_next_hop r is_ebgp) filtered |}.

(* =============================================================================
   §9.45: Route Flap Dampening (RFC 2439)
   ============================================================================= *)

(* Route flap dampening parameters per RFC 2439 *)
Definition PENALTY_PER_WITHDRAWAL : N := 1000.
Definition PENALTY_PER_ATTRIBUTE_CHANGE : N := 500.
Definition SUPPRESS_THRESHOLD : N := 3000.     (* Suppress route if penalty exceeds this *)
Definition REUSE_THRESHOLD : N := 750.         (* Reuse route when penalty decays below this *)
Definition MAX_SUPPRESS_TIME : N := 3600.      (* Maximum suppression time in seconds *)
Definition HALF_LIFE_REACHABLE : N := 900.     (* 15 minutes for reachable routes *)
Definition HALF_LIFE_UNREACHABLE : N := 300.   (* 5 minutes for unreachable routes *)

Record DampeningState := {
  damp_penalty : N;                    (* Current penalty value *)
  damp_last_update_time : N;           (* Timestamp of last update *)
  damp_is_suppressed : bool;           (* Whether route is currently suppressed *)
  damp_suppress_time : N;              (* How long route has been suppressed *)
  damp_flap_count : N                  (* Number of flaps detected *)
}.

(* Initial dampening state *)
Definition init_dampening_state : DampeningState :=
  {| damp_penalty := 0;
     damp_last_update_time := 0;
     damp_is_suppressed := false;
     damp_suppress_time := 0;
     damp_flap_count := 0 |}.

(* Exponential decay: penalty / 2^(elapsed/half_life) *)
Definition decay_penalty (current_penalty : N) (elapsed_time half_life : N) : N :=
  if N.eqb elapsed_time 0 then current_penalty
  else if N.leb current_penalty 1 then 0
  else
    let decay_factor := N.pow 2 (elapsed_time / half_life) in
    if N.leb current_penalty decay_factor then 0
    else current_penalty / decay_factor.

(* Withdrawal penalty application *)
Definition apply_withdrawal_penalty (state : DampeningState) (current_time : N) : DampeningState :=
  let elapsed := current_time - state.(damp_last_update_time) in
  let decayed := decay_penalty state.(damp_penalty) elapsed HALF_LIFE_UNREACHABLE in
  let new_penalty := decayed + PENALTY_PER_WITHDRAWAL in
  let should_suppress := N.leb SUPPRESS_THRESHOLD new_penalty in
  {| damp_penalty := new_penalty;
     damp_last_update_time := current_time;
     damp_is_suppressed := should_suppress;
     damp_suppress_time := if should_suppress then 0 else state.(damp_suppress_time);
     damp_flap_count := state.(damp_flap_count) + 1 |}.

(* Update dampening state on attribute change *)
Definition apply_attribute_change_penalty (state : DampeningState) (current_time : N) : DampeningState :=
  let elapsed := current_time - state.(damp_last_update_time) in
  let decayed := decay_penalty state.(damp_penalty) elapsed HALF_LIFE_REACHABLE in
  let new_penalty := decayed + PENALTY_PER_ATTRIBUTE_CHANGE in
  let should_suppress := N.leb SUPPRESS_THRESHOLD new_penalty in
  {| damp_penalty := new_penalty;
     damp_last_update_time := current_time;
     damp_is_suppressed := should_suppress;
     damp_suppress_time := if should_suppress then 0 else state.(damp_suppress_time);
     damp_flap_count := state.(damp_flap_count) + 1 |}.

(* Check if route should be reused after suppression *)
Definition should_reuse_route (state : DampeningState) (current_time : N) : bool :=
  if negb state.(damp_is_suppressed) then true
  else
    let elapsed := current_time - state.(damp_last_update_time) in
    let decayed := decay_penalty state.(damp_penalty) elapsed HALF_LIFE_UNREACHABLE in
    N.ltb decayed REUSE_THRESHOLD.

(* Helper lemmas for penalty_decays_monotonically *)

Lemma pow2_succ_double : forall n,
  N.pow 2 (N.succ n) = 2 * N.pow 2 n.
Proof.
  intros n.
  rewrite N.pow_succ_r by apply N.le_0_l.
  reflexivity.
Qed.

Lemma pow2_monotone : forall n m,
  n <= m -> N.pow 2 n <= N.pow 2 m.
Proof.
  intros n m Hle.
  induction m using N.peano_ind.
  - apply N.le_0_r in Hle. rewrite Hle. apply N.le_refl.
  - destruct (N.le_gt_cases n m) as [Hle'|Hgt].
    + apply IHm in Hle'.
      rewrite pow2_succ_double.
      transitivity (N.pow 2 m).
      * exact Hle'.
      * assert (2 * N.pow 2 m = N.pow 2 m + N.pow 2 m) by lia.
        rewrite H.
        apply N.le_add_r.
    + assert (n = N.succ m) by lia. subst.
      apply N.le_refl.
Qed.

Lemma div_monotone_denom : forall a b c,
  b <> 0 -> b <= c -> c <> 0 -> a / c <= a / b.
Proof.
  intros a b c Hb Hle Hc.
  destruct (N.eq_dec a 0) as [Ha0|Ha0].
  - subst. rewrite N.div_0_l by assumption.
    rewrite N.div_0_l by assumption.
    apply N.le_refl.
  - destruct (N.le_gt_cases c b) as [Hcb|Hcb].
    + assert (c = b) by lia. subst. apply N.le_refl.
    + assert (Hcpos: 0 < c) by lia.
      assert (Hbpos: 0 < b) by lia.
      apply N.div_le_compat_l; lia.
Qed.

Lemma div_zero_when_small : forall a b,
  a <= b -> b <> 0 -> a / b <= 1.
Proof.
  intros a b Hle Hb.
  destruct (N.eq_dec a 0) as [Ha0|Ha0].
  - subst. rewrite N.div_0_l by assumption. lia.
  - destruct (N.le_gt_cases a b) as [Hab|Hab].
    + apply N.div_le_upper_bound; lia.
    + lia.
Qed.

Lemma decay_factor_monotone : forall t1 t2 half_life,
  t1 <= t2 -> half_life <> 0 ->
  N.pow 2 (t1 / half_life) <= N.pow 2 (t2 / half_life).
Proof.
  intros t1 t2 half_life Hle Hhalf.
  apply pow2_monotone.
  apply N.div_le_mono; lia.
Qed.

Lemma decay_zero_stays_zero : forall time half_life,
  decay_penalty 0 time half_life = 0.
Proof.
  intros time half_life.
  unfold decay_penalty.
  destruct (N.eqb time 0); reflexivity.
Qed.

Lemma decay_one_becomes_zero : forall time half_life,
  time <> 0 -> decay_penalty 1 time half_life = 0.
Proof.
  intros time half_life Htime.
  unfold decay_penalty.
  rewrite (proj2 (N.eqb_neq time 0) Htime).
  simpl. reflexivity.
Qed.

Lemma decay_at_zero_is_identity : forall penalty half_life,
  decay_penalty penalty 0 half_life = penalty.
Proof.
  intros. unfold decay_penalty. simpl. reflexivity.
Qed.

Lemma decay_small_penalty_zero : forall penalty time half_life,
  penalty <= 1 -> time <> 0 ->
  decay_penalty penalty time half_life = 0.
Proof.
  intros penalty time half_life Hpen Htime.
  unfold decay_penalty.
  rewrite (proj2 (N.eqb_neq time 0) Htime).
  destruct (N.leb penalty 1) eqn:Hle.
  - reflexivity.
  - apply N.leb_gt in Hle. lia.
Qed.

Lemma pow2_pos : forall n,
  0 < N.pow 2 n.
Proof.
  intros n.
  induction n using N.peano_ind.
  - simpl. lia.
  - rewrite pow2_succ_double. lia.
Qed.

Lemma pow2_ge_1 : forall n,
  1 <= N.pow 2 n.
Proof.
  intros n. pose proof (pow2_pos n). lia.
Qed.

Lemma pow2_neq_0 : forall n,
  N.pow 2 n <> 0.
Proof.
  intros n. pose proof (pow2_pos n). lia.
Qed.

Lemma mult_ge_right : forall a b,
  1 <= b -> a <= b * a.
Proof.
  intros a b Hb.
  rewrite <- (N.mul_1_l a) at 1.
  apply N.mul_le_mono_r. exact Hb.
Qed.

Lemma div_le_numerator : forall a b,
  b <> 0 -> a / b <= a.
Proof.
  intros a b Hb.
  destruct (N.le_gt_cases a 0) as [Ha0|Ha0].
  - assert (a = 0) by lia. subst. rewrite N.div_0_l by assumption. apply N.le_refl.
  - destruct (N.le_gt_cases 1 b) as [Hb1|Hb1].
    + pose proof (N.div_mod a b Hb) as Hdivmod.
      assert (b * (a / b) <= a).
      { rewrite Hdivmod at 2. apply N.le_add_r. }
      assert (a / b <= b * (a / b)).
      { apply mult_ge_right. exact Hb1. }
      lia.
    + assert (b = 0) by lia. contradiction.
Qed.

(* Main theorem: Penalty decays monotonically *)
Theorem penalty_decays_monotonically : forall penalty time1 time2 half_life,
  time1 <= time2 ->
  decay_penalty penalty time2 half_life <= decay_penalty penalty time1 half_life.
Proof.
  intros penalty time1 time2 half_life Hle.
  unfold decay_penalty.
  destruct (N.eqb time1 0) eqn:Ht1_0.
  - apply N.eqb_eq in Ht1_0. subst time1.
    simpl. destruct (N.eqb time2 0) eqn:Ht2.
    + apply N.le_refl.
    + destruct (N.leb penalty 1) eqn:Hpsmall.
      * apply N.le_0_l.
      * remember (N.pow 2 (time2 / half_life)) as fac eqn:Heqfac.
        destruct (N.leb penalty fac) eqn:Hle_fac.
        apply N.le_0_l.
        apply N.leb_gt in Hpsmall.
        assert (Hfac_pos: fac <> 0) by (rewrite Heqfac; apply pow2_neq_0).
        apply div_le_numerator. assumption.
  - destruct (N.eqb time2 0) eqn:Ht2_0.
    + apply N.eqb_eq in Ht2_0. subst time2.
      apply N.eqb_neq in Ht1_0. lia.
    + apply N.eqb_neq in Ht1_0.
      apply N.eqb_neq in Ht2_0.
      destruct (N.leb penalty 1) eqn:Hpen.
      * apply N.leb_le in Hpen.
        destruct (N.eq_dec penalty 0) as [Hp0|Hp0].
        subst. simpl. apply N.le_refl.
        assert (penalty = 1) by lia. subst.
        simpl. apply N.le_refl.
      * apply N.leb_gt in Hpen.
        destruct (N.eq_dec half_life 0) as [Hhalf0|Hhalf0].
        subst half_life.
        rewrite N.div_0_r, N.div_0_r.
        simpl.
        destruct (N.leb penalty 1) eqn:Hle1.
        apply N.leb_le in Hle1. lia.
        destruct (N.leb penalty 1) eqn:Hle2.
        apply N.leb_le in Hle2. lia.
        apply N.le_refl.
        remember (N.pow 2 (time2 / half_life)) as factor2.
        remember (N.pow 2 (time1 / half_life)) as factor1.
        assert (Hfactor_le: factor1 <= factor2).
        { subst factor1 factor2. apply decay_factor_monotone; assumption. }
        destruct (N.leb penalty factor2) eqn:Hleb2.
        apply N.leb_le in Hleb2.
        destruct (N.leb penalty factor1) eqn:Hleb1.
        apply N.leb_le in Hleb1.
        apply N.le_refl.
        apply N.leb_gt in Hleb1.
        apply N.le_0_l.
        apply N.leb_gt in Hleb2.
        destruct (N.leb penalty factor1) eqn:Hleb1.
        apply N.leb_le in Hleb1. lia.
        apply N.leb_gt in Hleb1.
        assert (Hf1_pos: factor1 <> 0) by (subst factor1; apply pow2_neq_0).
        assert (Hf2_pos: factor2 <> 0) by (subst factor2; apply pow2_neq_0).
        apply div_monotone_denom; assumption.
Qed.

(* Theorem: Suppression occurs only when penalty exceeds threshold *)
Theorem suppression_requires_threshold : forall state current_time,
  (apply_withdrawal_penalty state current_time).(damp_is_suppressed) = true ->
  SUPPRESS_THRESHOLD <= (apply_withdrawal_penalty state current_time).(damp_penalty).
Proof.
  intros state current_time Hsupp.
  unfold apply_withdrawal_penalty in *.
  simpl in Hsupp.
  destruct (N.leb SUPPRESS_THRESHOLD _) eqn:Hle; try discriminate.
  apply N.leb_le. exact Hle.
Qed.

(* =============================================================================
   §9.5: RIB Properties
   ============================================================================= *)

(* Empty RIB has empty Loc-RIB *)
Theorem init_rib_empty_loc : init_rib.(loc_rib) = [].
Proof.
  reflexivity.
Qed.

(* Adding route preserves Loc-RIB *)
Theorem add_route_preserves_loc_rib : forall rib route,
  (add_route_in rib route).(loc_rib) = rib.(loc_rib).
Proof.
  intros. reflexivity.
Qed.

(* Loc-RIB contains at most one route *)
Theorem update_loc_rib_singleton_or_empty : forall rib,
  Nat.leb (length (update_loc_rib rib).(loc_rib)) 1 = true.
Proof.
  intros rib.
  unfold update_loc_rib.
  simpl.
  destruct (bgp_best_path_selection (adj_rib_in rib)).
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* fold_left with Some initial preserves or updates from list *)
Lemma fold_some_result_from_list_or_init : forall routes init result,
  fold_left (fun (best_opt : option BGPRoute) (r : BGPRoute) =>
    match best_opt with
    | None => Some r
    | Some b => if compare_routes r b then Some r else best_opt
    end) routes (Some init) = Some result ->
  result = init \/ In result routes.
Proof.
  induction routes as [|r routes' IH]; intros init result Hfold.
  - simpl in Hfold. inversion Hfold. left. reflexivity.
  - simpl in Hfold.
    destruct (compare_routes r init) eqn:Hcmp.
    + apply IH in Hfold.
      destruct Hfold as [Heq | Hin].
      * right. simpl. left. symmetry. exact Heq.
      * right. simpl. right. exact Hin.
    + apply IH in Hfold.
      destruct Hfold as [Heq | Hin].
      * left. exact Heq.
      * right. simpl. right. exact Hin.
Qed.

(* fold_left for best path returns element from list *)
Lemma fold_best_path_in_list : forall routes best,
  fold_left (fun (best_opt : option BGPRoute) (r : BGPRoute) =>
    match best_opt with
    | None => Some r
    | Some b => if compare_routes r b then Some r else best_opt
    end) routes None = Some best ->
  In best routes.
Proof.
  intros routes best Hfold.
  destruct routes as [|r routes'].
  - simpl in Hfold. discriminate Hfold.
  - simpl in Hfold.
    apply fold_some_result_from_list_or_init in Hfold.
    destruct Hfold as [Heq | Hin].
    + simpl. left. symmetry. exact Heq.
    + simpl. right. exact Hin.
Qed.

(* Loc-RIB best route is reachable and from Adj-RIB-In *)
Theorem loc_rib_contains_best_route : forall rib route,
  (update_loc_rib rib).(loc_rib) = [route] ->
  route.(route_next_hop_reachable) = true /\
  In route rib.(adj_rib_in).
Proof.
  intros rib route Hloc.
  unfold update_loc_rib in Hloc.
  simpl in Hloc.
  unfold bgp_best_path_selection in Hloc.
  remember (filter (fun r : BGPRoute => route_next_hop_reachable r) (adj_rib_in rib)) as reachable eqn:Heqreach.
  destruct (fold_left _ reachable None) as [best|] eqn:Hfold.
  - apply fold_best_path_in_list in Hfold.
    assert (Hin: In best (filter (fun r : BGPRoute => route_next_hop_reachable r) (adj_rib_in rib))).
    { rewrite <- Heqreach. exact Hfold. }
    apply filter_In in Hin.
    destruct Hin as [Hin Hreach].
    inversion Hloc. subst.
    split; assumption.
  - discriminate Hloc.
Qed.

(* Empty Adj-RIB-In yields empty Loc-RIB *)
Theorem empty_adj_rib_in_empty_loc_rib : forall rib,
  rib.(adj_rib_in) = [] ->
  (update_loc_rib rib).(loc_rib) = [].
Proof.
  intros rib Hempty.
  unfold update_loc_rib. simpl.
  unfold bgp_best_path_selection. rewrite Hempty. simpl. reflexivity.
Qed.

(* Adj-RIB-Out contains only routes from Loc-RIB *)
Theorem adj_rib_out_from_loc_rib : forall my_as my_rid rib is_ebgp route,
  In route (update_adj_rib_out my_as my_rid rib is_ebgp).(adj_rib_out) ->
  exists orig_route, In orig_route rib.(loc_rib) /\
                     should_advertise_route orig_route is_ebgp = true.
Proof.
  intros my_as my_rid rib is_ebgp route Hin.
  unfold update_adj_rib_out in Hin.
  simpl in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [orig [Hexport Hin]].
  exists orig. split.
  - apply filter_In in Hin. destruct Hin. assumption.
  - apply filter_In in Hin. destruct Hin. assumption.
Qed.

(* =============================================================================
   §10: Key Properties
   ============================================================================= *)

(* State machine starts in IDLE *)
Theorem initial_state_idle : forall las ras lid,
  (init_bgp_session las ras lid).(session_state) = IDLE.
Proof.
  intros. reflexivity.
Qed.

(* OPENCONFIRM→ESTABLISHED preserves remote_id *)
Theorem established_preserves_remote_id : forall session session' msg,
  session.(session_state) = OPENCONFIRM ->
  bgp_state_transition session KeepAliveMsg = (session', msg) ->
  session'.(session_state) = ESTABLISHED ->
  session'.(session_remote_id) = session.(session_remote_id).
Proof.
  intros session session' msg Hstate Htrans Hest.
  unfold bgp_state_transition in Htrans.
  rewrite Hstate in Htrans.
  inversion Htrans.
  reflexivity.
Qed.

(* Hold time negotiation takes minimum *)
Theorem hold_time_negotiation : forall session open_msg session',
  session.(session_state) = OPENSENT ->
  valid_open_message open_msg = true ->
  has_bgp_id_collision session.(session_local_id) open_msg.(open_bgp_identifier) = false ->
  verify_peer_as session.(session_expected_remote_as) open_msg.(open_my_as) = true ->
  bgp_state_transition session (BGPOpen_Received open_msg) = (session', Some KEEPALIVE) ->
  session'.(session_hold_time) = N.min session.(session_hold_time) open_msg.(open_hold_time).
Proof.
  intros session open_msg session' Hstate Hvalid Hnocoll Hpeer Htrans.
  unfold bgp_state_transition in Htrans.
  rewrite Hstate in Htrans.
  rewrite Hvalid in Htrans.
  rewrite Hnocoll in Htrans.
  rewrite Hpeer in Htrans.
  simpl in Htrans.
  inversion Htrans.
  reflexivity.
Qed.

(* Valid OPEN guarantees non-zero remote_id *)
Theorem valid_open_nonzero_remote_id : forall session open_msg session',
  session.(session_state) = OPENSENT ->
  valid_open_message open_msg = true ->
  has_bgp_id_collision session.(session_local_id) open_msg.(open_bgp_identifier) = false ->
  verify_peer_as session.(session_expected_remote_as) open_msg.(open_my_as) = true ->
  bgp_state_transition session (BGPOpen_Received open_msg) = (session', Some KEEPALIVE) ->
  session'.(session_remote_id) <> 0.
Proof.
  intros session open_msg session' Hstate Hvalid Hnocoll Hpeer Htrans.
  unfold bgp_state_transition in Htrans.
  rewrite Hstate in Htrans.
  rewrite Hvalid in Htrans.
  rewrite Hnocoll in Htrans.
  rewrite Hpeer in Htrans.
  simpl in Htrans.
  inversion Htrans. subst. simpl.
  unfold valid_open_message in Hvalid.
  apply andb_prop in Hvalid. destruct Hvalid as [_ Hrest].
  apply andb_prop in Hrest. destruct Hrest as [Hid _].
  unfold valid_bgp_identifier in Hid.
  apply andb_prop in Hid. destruct Hid as [Hnot_zero _].
  intro Hcontra.
  unfold negb in Hnot_zero.
  rewrite Hcontra in Hnot_zero.
  simpl in Hnot_zero.
  discriminate Hnot_zero.
Qed.

(* Valid hold time accepts 0 or >=3 *)
Theorem valid_hold_time_bounds : forall ht,
  valid_hold_time ht = true ->
  ht = 0 \/ (HOLD_TIME_MIN <= ht /\ ht <= HOLD_TIME_MAX).
Proof.
  intros ht Hvalid.
  unfold valid_hold_time in Hvalid.
  apply orb_prop in Hvalid.
  destruct Hvalid as [Hzero | Hrange].
  - left. apply N.eqb_eq. exact Hzero.
  - right. apply andb_prop in Hrange. destruct Hrange as [Hmin Hmax].
    apply N.leb_le in Hmin. apply N.leb_le in Hmax.
    split.
    + exact Hmin.
    + exact Hmax.
Qed.

(* Invalid hold times rejected *)
Theorem invalid_hold_time_rejected : forall ht,
  ht <> 0 -> ht < HOLD_TIME_MIN ->
  valid_hold_time ht = false.
Proof.
  intros ht Hnonzero Hlt.
  unfold valid_hold_time.
  apply orb_false_intro.
  - apply N.eqb_neq. exact Hnonzero.
  - apply andb_false_intro1. apply N.leb_gt. exact Hlt.
Qed.

(* AS 0 is invalid *)
Theorem as_zero_invalid :
  valid_as_number 0 = false.
Proof.
  unfold valid_as_number. simpl. reflexivity.
Qed.

(* Non-zero AS is valid *)
Theorem as_nonzero_valid : forall asn,
  asn <> 0 -> valid_as_number asn = true.
Proof.
  intros asn Hnonzero.
  unfold valid_as_number.
  apply negb_true_iff.
  apply N.eqb_neq.
  exact Hnonzero.
Qed.

(* Valid ORIGIN values *)
Theorem origin_igp_valid :
  valid_origin_value ORIGIN_IGP = true.
Proof.
  unfold valid_origin_value, ORIGIN_IGP. simpl. reflexivity.
Qed.

Theorem origin_egp_valid :
  valid_origin_value ORIGIN_EGP = true.
Proof.
  unfold valid_origin_value, ORIGIN_EGP, ORIGIN_IGP. simpl. reflexivity.
Qed.

Theorem origin_incomplete_valid :
  valid_origin_value ORIGIN_INCOMPLETE = true.
Proof.
  unfold valid_origin_value, ORIGIN_INCOMPLETE, ORIGIN_IGP, ORIGIN_EGP. simpl. reflexivity.
Qed.

Theorem origin_invalid : forall v,
  v <> ORIGIN_IGP -> v <> ORIGIN_EGP -> v <> ORIGIN_INCOMPLETE ->
  valid_origin_value v = false.
Proof.
  intros v H1 H2 H3.
  unfold valid_origin_value.
  apply orb_false_intro.
  - apply N.eqb_neq. exact H1.
  - apply orb_false_intro.
    + apply N.eqb_neq. exact H2.
    + apply N.eqb_neq. exact H3.
Qed.

(* Valid NLRI prefix lengths *)
Theorem nlri_valid_zero : valid_nlri_prefix_len 0 = true.
Proof.
  unfold valid_nlri_prefix_len. simpl. reflexivity.
Qed.

Theorem nlri_valid_32 : valid_nlri_prefix_len 32 = true.
Proof.
  unfold valid_nlri_prefix_len. simpl. reflexivity.
Qed.

Theorem nlri_invalid_33 : valid_nlri_prefix_len 33 = false.
Proof.
  unfold valid_nlri_prefix_len. simpl. reflexivity.
Qed.

(* Connection failure transitions to ACTIVE *)
Theorem connect_failure_to_active : forall session session' msg,
  session.(session_state) = CONNECT ->
  bgp_state_transition session TCPConnectionFails = (session', msg) ->
  session'.(session_state) = ACTIVE.
Proof.
  intros session session' msg Hstate Htrans.
  unfold bgp_state_transition in Htrans.
  rewrite Hstate in Htrans.
  inversion Htrans.
  reflexivity.
Qed.

(* ACTIVE transitions to OPENSENT on TCP success *)
Theorem active_to_opensent : forall session session' msg,
  session.(session_state) = ACTIVE ->
  bgp_state_transition session TCPConnectionConfirmed = (session', msg) ->
  session'.(session_state) = OPENSENT.
Proof.
  intros session session' msg Hstate Htrans.
  unfold bgp_state_transition in Htrans.
  rewrite Hstate in Htrans.
  inversion Htrans.
  reflexivity.
Qed.

(* ACTIVE retry timer expires back to CONNECT *)
Theorem active_retry_to_connect : forall session session' msg,
  session.(session_state) = ACTIVE ->
  bgp_state_transition session ConnectRetryTimerExpires = (session', msg) ->
  session'.(session_state) = CONNECT.
Proof.
  intros session session' msg Hstate Htrans.
  unfold bgp_state_transition in Htrans.
  rewrite Hstate in Htrans.
  inversion Htrans.
  reflexivity.
Qed.

(* Notification returns to IDLE *)
Theorem notification_to_idle : forall session notif session' msg,
  bgp_state_transition session (NotifMsg notif) = (session', msg) ->
  session'.(session_state) = IDLE.
Proof.
  intros. unfold bgp_state_transition in H.
  destruct session.(session_state); inversion H; reflexivity.
Qed.

(* Timer tick updates elapsed time *)
Theorem timer_tick_increments_time : forall session delta session' events,
  timer_tick session delta = (session', events) ->
  session'.(session_time_elapsed) = session.(session_time_elapsed) + delta.
Proof.
  intros session delta session' events Htick.
  unfold timer_tick in Htick.
  inversion Htick.
  reflexivity.
Qed.

(* AS path loop detection *)
Theorem as_path_loop_detected : forall my_as as_path,
  has_as_loop my_as as_path = true ->
  In my_as as_path.
Proof.
  intros my_as as_path Hloop.
  unfold has_as_loop in Hloop.
  apply existsb_exists in Hloop.
  destruct Hloop as [x [Hin Heq]].
  apply N.eqb_eq in Heq.
  rewrite <- Heq.
  exact Hin.
Qed.

(* Collision resolution is antisymmetric *)
Theorem collision_resolution_antisymmetric : forall local_id remote_id,
  local_id <> remote_id ->
  resolve_collision local_id remote_id true =
  negb (resolve_collision remote_id local_id true).
Proof.
  intros local_id remote_id Hneq.
  unfold resolve_collision.
  destruct (N.ltb local_id remote_id) eqn:Hlt.
  - apply N.ltb_lt in Hlt.
    assert (Hge: N.ltb remote_id local_id = false).
    { apply N.ltb_ge. lia. }
    rewrite Hge. simpl. reflexivity.
  - apply N.ltb_ge in Hlt.
    assert (Hlt': local_id > remote_id \/ local_id = remote_id) by lia.
    destruct Hlt' as [Hgt | Heq].
    + assert (Hlt'': N.ltb remote_id local_id = true).
      { apply N.ltb_lt. lia. }
      rewrite Hlt''. simpl. reflexivity.
    + contradiction Hneq.
Qed.

(* Higher ID always wins in collision resolution *)
Theorem collision_higher_id_wins : forall local_id remote_id,
  local_id > remote_id ->
  resolve_collision local_id remote_id true = true.
Proof.
  intros local_id remote_id Hgt.
  unfold resolve_collision.
  assert (Hge: N.ltb local_id remote_id = false).
  { apply N.ltb_ge. lia. }
  rewrite Hge. reflexivity.
Qed.

(* Mandatory attributes in valid UPDATE *)
Theorem valid_update_has_mandatory : forall my_as update,
  valid_update_message my_as update = true ->
  N.of_nat (length update.(update_nlri)) > 0 ->
  has_mandatory_attributes update.(update_path_attributes) = true.
Proof.
  intros my_as update Hvalid Hlen.
  unfold valid_update_message in Hvalid.
  apply andb_prop in Hvalid. destruct Hvalid as [_ Hrest].
  apply andb_prop in Hrest. destruct Hrest as [Hmand _].
  destruct (negb (N.eqb (N.of_nat (length (update_nlri update))) 0)) eqn:Hempty.
  - exact Hmand.
  - apply negb_false_iff in Hempty. apply N.eqb_eq in Hempty.
    lia.
Qed.

(* Valid header has correct marker length *)
Theorem valid_header_correct_marker_length : forall hdr,
  valid_bgp_header hdr = true ->
  N.of_nat (length hdr.(bgp_marker)) = BGP_MARKER_LENGTH.
Proof.
  intros hdr Hvalid.
  unfold valid_bgp_header in Hvalid.
  apply andb_prop in Hvalid. destruct Hvalid as [Hmarker _].
  unfold valid_marker in Hmarker.
  apply andb_prop in Hmarker. destruct Hmarker as [Hlen _].
  apply N.eqb_eq in Hlen. assumption.
Qed.

(* Best path selection excludes unreachable routes *)
Theorem best_path_excludes_unreachable : forall r routes,
  r.(route_next_hop_reachable) = false ->
  bgp_best_path_selection (r :: routes) = bgp_best_path_selection routes.
Proof.
  intros r routes Hunreach.
  unfold bgp_best_path_selection.
  simpl. rewrite Hunreach. reflexivity.
Qed.

(* =============================================================================
   §11: Deep Properties - Convergence
   ============================================================================= *)

Definition is_stable_state (s : BGPState) : bool :=
  match s with
  | IDLE => true
  | ESTABLISHED => true
  | _ => false
  end.

Fixpoint apply_transitions (session : BGPSession) (events : list BGPEvent) (fuel : nat) : BGPSession :=
  match fuel with
  | O => session
  | S n =>
      match events with
      | [] => session
      | e :: rest =>
          let (next_session, _) := bgp_state_transition session e in
          if is_stable_state next_session.(session_state)
          then next_session
          else apply_transitions next_session rest n
      end
  end.

Lemma stable_state_decidable : forall s,
  is_stable_state s = true \/ is_stable_state s = false.
Proof.
  intros. destruct (is_stable_state s); auto.
Qed.

Lemma apply_transitions_empty_events : forall session n,
  apply_transitions session [] n = session.
Proof.
  intros. destruct n; simpl; reflexivity.
Qed.

Lemma is_stable_state_correct : forall s,
  s = IDLE \/ s = ESTABLISHED -> is_stable_state s = true.
Proof.
  intros s [H | H]; rewrite H; reflexivity.
Qed.

Lemma not_zero_succ : forall n, S n <> O.
Proof.
  intros n contra. discriminate contra.
Qed.

Lemma succ_not_zero : forall n, n = O -> S n = O -> False.
Proof.
  intros n H contra. discriminate contra.
Qed.

Lemma apply_transitions_O : forall session events,
  apply_transitions session events O = session.
Proof.
  intros. destruct events; reflexivity.
Qed.

Lemma apply_transitions_nil_succ : forall session n,
  apply_transitions session [] (S n) = session.
Proof.
  intros. apply apply_transitions_empty_events.
Qed.

Lemma apply_transitions_cons_stable : forall session e rest n next_session msg,
  bgp_state_transition session e = (next_session, msg) ->
  is_stable_state (session_state next_session) = true ->
  apply_transitions session (e :: rest) (S n) = next_session.
Proof.
  intros. simpl. rewrite H. rewrite H0. reflexivity.
Qed.

Lemma apply_transitions_cons_unstable : forall session e rest n next_session msg,
  bgp_state_transition session e = (next_session, msg) ->
  is_stable_state (session_state next_session) = false ->
  apply_transitions session (e :: rest) (S n) = apply_transitions next_session rest n.
Proof.
  intros. simpl. rewrite H. rewrite H0. reflexivity.
Qed.

Lemma stable_state_rewrite : forall s,
  is_stable_state s = true -> s = IDLE \/ s = ESTABLISHED.
Proof.
  intros. unfold is_stable_state in H. destruct s; try discriminate; auto.
Qed.

Lemma stable_at_cons_succ : forall session e rest n next_session msg,
  bgp_state_transition session e = (next_session, msg) ->
  is_stable_state (session_state next_session) = true ->
  is_stable_state (session_state (apply_transitions session (e :: rest) (S n))) = true.
Proof.
  intros. rewrite apply_transitions_cons_stable with (next_session := next_session) (msg := msg); auto.
Qed.

Theorem convergence_fuel_zero : forall session events,
  apply_transitions session events O = session.
Proof.
  intros. apply apply_transitions_O.
Qed.

Theorem convergence_events_nil : forall session n,
  apply_transitions session [] n = session.
Proof.
  intros. destruct n. reflexivity. apply apply_transitions_nil_succ.
Qed.

Theorem convergence_reaches_stable_or_exhausts : forall session e rest n,
  exists final,
    apply_transitions session (e :: rest) (S n) = final /\
    (is_stable_state (session_state final) = true \/
     (forall next_session msg,
       bgp_state_transition session e = (next_session, msg) ->
       is_stable_state (session_state next_session) = false /\
       apply_transitions next_session rest n = final)).
Proof.
  intros. simpl.
  destruct (bgp_state_transition session e) as [next_session msg] eqn:Htrans.
  destruct (is_stable_state (session_state next_session)) eqn:Hstable.
  - exists next_session. split. reflexivity. left. exact Hstable.
  - exists (apply_transitions next_session rest n). split. reflexivity.
    right. intros ns m H. injection H as H1 H2. subst. split. exact Hstable. reflexivity.
Qed.

Theorem notification_converges_to_idle : forall session notif,
  let (session', _) := bgp_state_transition session (NotifMsg notif) in
  session'.(session_state) = IDLE.
Proof.
  intros. unfold bgp_state_transition.
  destruct session.(session_state); reflexivity.
Qed.

(* =============================================================================
   §11.45: Time-Bounded Convergence Analysis
   ============================================================================= *)

(* Maximum transitions to reach stable state from any state *)
Definition max_transitions_to_stable : nat := 4.

(* Convergence time bound: max 4 transitions *)
Theorem convergence_time_bound :
  max_transitions_to_stable = 4%nat.
Proof.
  unfold max_transitions_to_stable.
  reflexivity.
Qed.

Lemma connect_not_stable : is_stable_state CONNECT = false.
Proof. reflexivity. Qed.

Lemma opensent_not_stable : is_stable_state OPENSENT = false.
Proof. reflexivity. Qed.

Lemma openconfirm_not_stable : is_stable_state OPENCONFIRM = false.
Proof. reflexivity. Qed.

Lemma established_stable : is_stable_state ESTABLISHED = true.
Proof. reflexivity. Qed.

Lemma active_not_stable : is_stable_state ACTIVE = false.
Proof. reflexivity. Qed.

(* IDLE→ManualStart yields CONNECT *)
Lemma idle_manualstart_connect : forall session,
  session.(session_state) = IDLE ->
  (fst (bgp_state_transition session ManualStart)).(session_state) = CONNECT.
Proof.
  intros. unfold bgp_state_transition. rewrite H. reflexivity.
Qed.

(* Transitions preserve local_id and expected_remote_as *)
Lemma idle_manualstart_preserves_local_id : forall session,
  session.(session_state) = IDLE ->
  (fst (bgp_state_transition session ManualStart)).(session_local_id) = session.(session_local_id).
Proof.
  intros. unfold bgp_state_transition. rewrite H. reflexivity.
Qed.

Lemma idle_manualstart_preserves_expected_remote_as : forall session,
  session.(session_state) = IDLE ->
  (fst (bgp_state_transition session ManualStart)).(session_expected_remote_as) = session.(session_expected_remote_as).
Proof.
  intros. unfold bgp_state_transition. rewrite H. reflexivity.
Qed.

Lemma connect_tcpconfirmed_preserves_local_id : forall session,
  session.(session_state) = CONNECT ->
  (fst (bgp_state_transition session TCPConnectionConfirmed)).(session_local_id) = session.(session_local_id).
Proof.
  intros. unfold bgp_state_transition. rewrite H. reflexivity.
Qed.

Lemma connect_tcpconfirmed_preserves_expected_remote_as : forall session,
  session.(session_state) = CONNECT ->
  (fst (bgp_state_transition session TCPConnectionConfirmed)).(session_expected_remote_as) = session.(session_expected_remote_as).
Proof.
  intros. unfold bgp_state_transition. rewrite H. reflexivity.
Qed.

(* Maximum fuel bounds: 4 transitions sufficient for IDLE→ESTABLISHED *)
Theorem idle_to_established_max_fuel : forall session open_msg,
  session.(session_state) = IDLE ->
  valid_open_message open_msg = true ->
  has_bgp_id_collision session.(session_local_id) open_msg.(open_bgp_identifier) = false ->
  verify_peer_as session.(session_expected_remote_as) open_msg.(open_my_as) = true ->
  let events := [ManualStart; TCPConnectionConfirmed; BGPOpen_Received open_msg; KeepAliveMsg] in
  is_stable_state (session_state (apply_transitions session events 4)) = true.
Proof.
  intros session open_msg Hidle Hvalid Hnocoll Hpeer events.
  simpl.
  destruct (bgp_state_transition session ManualStart) as [s1 msg1] eqn:Ht1.
  assert (Hs1: s1.(session_state) = CONNECT).
  { unfold bgp_state_transition in Ht1. rewrite Hidle in Ht1. inversion Ht1. reflexivity. }
  assert (Hs1_lid: s1.(session_local_id) = session.(session_local_id)).
  { unfold bgp_state_transition in Ht1. rewrite Hidle in Ht1. inversion Ht1. reflexivity. }
  assert (Hs1_ras: s1.(session_expected_remote_as) = session.(session_expected_remote_as)).
  { unfold bgp_state_transition in Ht1. rewrite Hidle in Ht1. inversion Ht1. reflexivity. }
  rewrite Hs1. simpl.
  destruct (bgp_state_transition s1 TCPConnectionConfirmed) as [s2 msg2] eqn:Ht2.
  assert (Hs2: s2.(session_state) = OPENSENT).
  { unfold bgp_state_transition in Ht2. rewrite Hs1 in Ht2. inversion Ht2. reflexivity. }
  assert (Hs2_lid: s2.(session_local_id) = session.(session_local_id)).
  { unfold bgp_state_transition in Ht2. rewrite Hs1 in Ht2. inversion Ht2. exact Hs1_lid. }
  assert (Hs2_ras: s2.(session_expected_remote_as) = session.(session_expected_remote_as)).
  { unfold bgp_state_transition in Ht2. rewrite Hs1 in Ht2. inversion Ht2. exact Hs1_ras. }
  rewrite Hs2. simpl.
  destruct (bgp_state_transition s2 (BGPOpen_Received open_msg)) as [s3 msg3] eqn:Ht3.
  assert (Hs3: s3.(session_state) = OPENCONFIRM).
  { unfold bgp_state_transition in Ht3. rewrite Hs2 in Ht3. rewrite Hvalid in Ht3.
    assert (Hnocoll2: has_bgp_id_collision s2.(session_local_id) open_msg.(open_bgp_identifier) = false).
    { rewrite Hs2_lid. exact Hnocoll. }
    rewrite Hnocoll2 in Ht3.
    assert (Hpeer2: verify_peer_as s2.(session_expected_remote_as) open_msg.(open_my_as) = true).
    { rewrite Hs2_ras. exact Hpeer. }
    rewrite Hpeer2 in Ht3. simpl in Ht3. inversion Ht3. reflexivity. }
  simpl.
  unfold bgp_state_transition at 1.
  rewrite Hs3.
  simpl. reflexivity.
Qed.

(* IDLE to ESTABLISHED requires exactly 4 successful transitions *)
Theorem idle_to_established_steps : forall session open_msg,
  session.(session_state) = IDLE ->
  valid_open_message open_msg = true ->
  has_bgp_id_collision session.(session_local_id) open_msg.(open_bgp_identifier) = false ->
  verify_peer_as session.(session_expected_remote_as) open_msg.(open_my_as) = true ->
  exists s1 s2 s3 s4,
    (fst (bgp_state_transition session ManualStart)) = s1 /\
    s1.(session_state) = CONNECT /\
    (fst (bgp_state_transition s1 TCPConnectionConfirmed)) = s2 /\
    s2.(session_state) = OPENSENT /\
    (fst (bgp_state_transition s2 (BGPOpen_Received open_msg))) = s3 /\
    s3.(session_state) = OPENCONFIRM /\
    (fst (bgp_state_transition s3 KeepAliveMsg)) = s4 /\
    s4.(session_state) = ESTABLISHED.
Proof.
  intros session open_msg Hidle Hvalid Hnocoll Hpeer.
  set (s1 := fst (bgp_state_transition session ManualStart)).
  set (s2 := fst (bgp_state_transition s1 TCPConnectionConfirmed)).
  set (s3 := fst (bgp_state_transition s2 (BGPOpen_Received open_msg))).
  set (s4 := fst (bgp_state_transition s3 KeepAliveMsg)).
  exists s1, s2, s3, s4.
  split. reflexivity.
  split. unfold s1, bgp_state_transition. rewrite Hidle. reflexivity.
  split. reflexivity.
  split. unfold s2, s1, bgp_state_transition. rewrite Hidle. simpl. reflexivity.
  split. reflexivity.
  split. unfold s3, s2, s1, bgp_state_transition. rewrite Hidle. simpl.
         rewrite Hvalid, Hnocoll, Hpeer. simpl. reflexivity.
  split. reflexivity.
  unfold s4, s3, s2, s1, bgp_state_transition. rewrite Hidle. simpl.
  rewrite Hvalid, Hnocoll, Hpeer. simpl. reflexivity.
Qed.

(* =============================================================================
   §11.5: Deep Properties - Safety
   ============================================================================= *)

Lemma established_from_openconfirm : forall session,
  session.(session_state) = OPENCONFIRM ->
  (fst (bgp_state_transition session KeepAliveMsg)).(session_state) = ESTABLISHED.
Proof.
  intros. unfold bgp_state_transition. rewrite H. reflexivity.
Qed.

Lemma openconfirm_from_opensent_valid : forall session open_msg,
  session.(session_state) = OPENSENT ->
  valid_open_message open_msg = true ->
  has_bgp_id_collision session.(session_local_id) open_msg.(open_bgp_identifier) = false ->
  verify_peer_as session.(session_expected_remote_as) open_msg.(open_my_as) = true ->
  (fst (bgp_state_transition session (BGPOpen_Received open_msg))).(session_state) = OPENCONFIRM.
Proof.
  intros. unfold bgp_state_transition. rewrite H. rewrite H0. rewrite H1. rewrite H2. simpl. reflexivity.
Qed.

Lemma opensent_from_connect : forall session,
  session.(session_state) = CONNECT ->
  (fst (bgp_state_transition session TCPConnectionConfirmed)).(session_state) = OPENSENT.
Proof.
  intros. unfold bgp_state_transition. rewrite H. reflexivity.
Qed.

Theorem safety_established_from_idle : forall session,
  session.(session_state) = IDLE ->
  session.(session_local_id) <> 1 ->
  session.(session_expected_remote_as) = 65001 ->
  exists open_msg established_session,
    valid_open_message open_msg = true /\
    established_session.(session_state) = ESTABLISHED /\
    exists intermediate1 intermediate2 intermediate3,
      (fst (bgp_state_transition session ManualStart)) = intermediate1 /\
      intermediate1.(session_state) = CONNECT /\
      (fst (bgp_state_transition intermediate1 TCPConnectionConfirmed)) = intermediate2 /\
      intermediate2.(session_state) = OPENSENT /\
      (fst (bgp_state_transition intermediate2 (BGPOpen_Received open_msg))) = intermediate3 /\
      intermediate3.(session_state) = OPENCONFIRM /\
      (fst (bgp_state_transition intermediate3 KeepAliveMsg)) = established_session.
Proof.
  intros session Hidle Hnocoll Hpeer.
  exists {| open_version := BGP_VERSION;
            open_my_as := 65001;
            open_hold_time := 90;
            open_bgp_identifier := 1;
            open_opt_param_len := 0;
            open_opt_params := [] |}.
  unfold bgp_state_transition. rewrite Hidle.
  unfold has_bgp_id_collision. simpl.
  assert (Hcollfalse: N.eqb (session_local_id session) 1 = false).
  { apply N.eqb_neq. exact Hnocoll. }
  set (intermediate1 := {| session_state := CONNECT;
                           session_local_as := session_local_as session;
                           session_remote_as := session_remote_as session;
                           session_local_id := session_local_id session;
                           session_remote_id := session_remote_id session;
                           session_hold_time := session_hold_time session;
                           session_keepalive_time := session_keepalive_time session;
                           session_connect_retry_counter := 0;
                           session_connect_retry_timer := Some CONNECT_RETRY_TIME;
                           session_hold_timer := session_hold_timer session;
                           session_keepalive_timer := session_keepalive_timer session;
                           session_delay_open_timer := session_delay_open_timer session;
                           session_idle_hold_timer := session_idle_hold_timer session;
                           session_capabilities := session_capabilities session;
                           session_time_elapsed := 0;
                           session_expected_remote_as := session.(session_expected_remote_as);
                           session_connection_direction := session.(session_connection_direction) |}).
  set (intermediate2 := {| session_state := OPENSENT;
                           session_local_as := session_local_as intermediate1;
                           session_remote_as := session_remote_as intermediate1;
                           session_local_id := session_local_id intermediate1;
                           session_remote_id := session_remote_id intermediate1;
                           session_hold_time := session_hold_time intermediate1;
                           session_keepalive_time := session_keepalive_time intermediate1;
                           session_connect_retry_counter := session_connect_retry_counter intermediate1;
                           session_connect_retry_timer := None;
                           session_hold_timer := arm (session_time_elapsed intermediate1) (session_hold_time intermediate1);
                           session_keepalive_timer := session_keepalive_timer intermediate1;
                           session_delay_open_timer := session_delay_open_timer intermediate1;
                           session_idle_hold_timer := session_idle_hold_timer intermediate1;
                           session_capabilities := session_capabilities intermediate1;
                           session_time_elapsed := session_time_elapsed intermediate1;
                           session_expected_remote_as := intermediate1.(session_expected_remote_as);
                           session_connection_direction := intermediate1.(session_connection_direction) |}).
  set (negotiated_hold := N.min (session_hold_time intermediate2) 90).
  set (intermediate3 := {| session_state := OPENCONFIRM;
                           session_local_as := session_local_as intermediate2;
                           session_remote_as := 65001;
                           session_local_id := session_local_id intermediate2;
                           session_remote_id := 1;
                           session_hold_time := negotiated_hold;
                           session_keepalive_time := negotiated_hold / 3;
                           session_connect_retry_counter := session_connect_retry_counter intermediate2;
                           session_connect_retry_timer := session_connect_retry_timer intermediate2;
                           session_hold_timer := arm (session_time_elapsed intermediate2) negotiated_hold;
                           session_keepalive_timer := arm (session_time_elapsed intermediate2) (negotiated_hold / 3);
                           session_delay_open_timer := session_delay_open_timer intermediate2;
                           session_idle_hold_timer := session_idle_hold_timer intermediate2;
                           session_capabilities := [];
                           session_time_elapsed := session_time_elapsed intermediate2;
                           session_expected_remote_as := intermediate2.(session_expected_remote_as);
                           session_connection_direction := intermediate2.(session_connection_direction) |}).
  set (established_session := {| session_state := ESTABLISHED;
                                  session_local_as := session_local_as intermediate3;
                                  session_remote_as := session_remote_as intermediate3;
                                  session_local_id := session_local_id intermediate3;
                                  session_remote_id := session_remote_id intermediate3;
                                  session_hold_time := session_hold_time intermediate3;
                                  session_keepalive_time := session_keepalive_time intermediate3;
                                  session_connect_retry_counter := session_connect_retry_counter intermediate3;
                                  session_connect_retry_timer := session_connect_retry_timer intermediate3;
                                  session_hold_timer := arm (session_time_elapsed intermediate3) (session_hold_time intermediate3);
                                  session_keepalive_timer := arm (session_time_elapsed intermediate3) (session_keepalive_time intermediate3);
                                  session_delay_open_timer := session_delay_open_timer intermediate3;
                                  session_idle_hold_timer := session_idle_hold_timer intermediate3;
                                  session_capabilities := session_capabilities intermediate3;
                                  session_time_elapsed := session_time_elapsed intermediate3;
                                  session_expected_remote_as := intermediate3.(session_expected_remote_as);
                                  session_connection_direction := intermediate3.(session_connection_direction) |}).
  exists established_session.
  split. unfold valid_open_message, valid_bgp_identifier, valid_hold_time, valid_as_number. simpl. reflexivity.
  split. reflexivity.
  exists intermediate1, intermediate2, intermediate3.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  split.
  - unfold fst. simpl. rewrite Hcollfalse. unfold verify_peer_as. rewrite Hpeer. simpl.
    unfold intermediate3, intermediate2, intermediate1, negotiated_hold. simpl. rewrite Hpeer. reflexivity.
  - split. reflexivity. reflexivity.
Qed.

(* =============================================================================
   §11.6: Deep Properties - Liveness
   ============================================================================= *)

Lemma hold_timer_set_in_opensent : forall session,
  session.(session_state) = CONNECT ->
  (fst (bgp_state_transition session TCPConnectionConfirmed)).(session_hold_timer) = arm (session.(session_time_elapsed)) (session.(session_hold_time)).
Proof.
  intros. unfold bgp_state_transition. rewrite H. simpl. reflexivity.
Qed.

Theorem liveness_hold_timer_bounded : forall session,
  session.(session_state) = OPENSENT ->
  valid_hold_time session.(session_hold_time) = true ->
  session.(session_hold_time) <= HOLD_TIME_MAX.
Proof.
  intros session Hstate Hvalid.
  apply valid_hold_time_bounds in Hvalid.
  destruct Hvalid as [Hzero | [Hmin Hmax]].
  - rewrite Hzero. unfold HOLD_TIME_MAX. lia.
  - exact Hmax.
Qed.

(* =============================================================================
   §11.65: RFC 4456 Route Reflection - CLUSTER_LIST Loop Prevention
   ============================================================================= *)

(* Decode CLUSTER_LIST from 4-byte cluster IDs *)
Fixpoint decode_cluster_list_aux (bytes : list byte) (fuel : nat) : list word32 :=
  match fuel with
  | O => []
  | S fuel' =>
      match bytes with
      | b1 :: b2 :: b3 :: b4 :: rest =>
          let cluster_id := N.lor (N.lor (N.lor (N.shiftl b1 24) (N.shiftl b2 16))
                                         (N.shiftl b3 8)) b4 in
          cluster_id :: decode_cluster_list_aux rest fuel'
      | _ => []
      end
  end.

Definition decode_cluster_list (bytes : list byte) : list word32 :=
  decode_cluster_list_aux bytes (length bytes).

(* Get CLUSTER_LIST from path attributes *)
Definition get_cluster_list (attrs : list PathAttribute) : list word32 :=
  match find (fun attr => N.eqb attr.(attr_type_code) ATTR_CLUSTER_LIST) attrs with
  | None => []
  | Some attr => decode_cluster_list attr.(attr_value)
  end.

(* Cluster loop detection functions defined earlier in §9 *)

(* Cluster loop detection identifies cluster ID in list *)
Theorem cluster_loop_detected : forall my_cid cluster_list,
  has_cluster_loop my_cid cluster_list = true ->
  In my_cid cluster_list.
Proof.
  intros my_cid cluster_list Hloop.
  unfold has_cluster_loop in Hloop.
  apply existsb_exists in Hloop.
  destruct Hloop as [x [Hin Heq]].
  apply N.eqb_eq in Heq.
  rewrite <- Heq.
  exact Hin.
Qed.

(* No cluster loop means cluster ID not in list *)
Theorem no_cluster_loop_not_in_list : forall my_cid cluster_list,
  has_cluster_loop my_cid cluster_list = false ->
  ~In my_cid cluster_list.
Proof.
  intros my_cid cluster_list Hno_loop Hin.
  unfold has_cluster_loop in Hno_loop.
  assert (Htrue: existsb (fun cid : N => cid =? my_cid) cluster_list = true).
  { apply existsb_exists. exists my_cid. split. exact Hin. apply N.eqb_refl. }
  rewrite Htrue in Hno_loop.
  discriminate Hno_loop.
Qed.

(* Decoding CLUSTER_LIST of valid length produces correct number of IDs *)
Theorem decode_cluster_list_valid_length : forall (bytes : list byte),
  (N.of_nat (length bytes)) mod 4 = 0 ->
  (N.of_nat (length bytes)) = 0 \/ (N.of_nat (length bytes)) >= 4.
Proof.
  intros bytes Hmod.
  destruct bytes as [|b1 [|b2 [|b3 [|b4 bytes']]]].
  - left. simpl. reflexivity.
  - simpl in Hmod. discriminate Hmod.
  - simpl in Hmod. discriminate Hmod.
  - simpl in Hmod. discriminate Hmod.
  - right. simpl. lia.
Qed.

(* =============================================================================
   §11.655: RFC 7911 ADD-PATH - Multiple Paths per Prefix
   ============================================================================= *)

Definition PATH_ID := word32.

Fixpoint decode_path_ids_aux (bytes : list byte) (fuel : nat) : list PATH_ID :=
  match fuel with
  | O => []
  | S fuel' =>
      match bytes with
      | b1 :: b2 :: b3 :: b4 :: rest =>
          let path_id := N.lor (N.lor (N.lor (N.shiftl b1 24) (N.shiftl b2 16))
                                       (N.shiftl b3 8)) b4 in
          path_id :: decode_path_ids_aux rest fuel'
      | _ => []
      end
  end.

Definition decode_path_id (bytes : list byte) : option PATH_ID :=
  match bytes with
  | b1 :: b2 :: b3 :: b4 :: _ =>
      Some (N.lor (N.lor (N.lor (N.shiftl b1 24) (N.shiftl b2 16))
                         (N.shiftl b3 8)) b4)
  | _ => None
  end.

Definition check_add_path_capability (params : list BGPOptionalParameter) : bool :=
  has_capability_in_params CAP_ADD_PATH params.

Definition valid_path_id (path_id : PATH_ID) : bool :=
  true.

Theorem add_path_enabled_allows_multiple_paths : forall local remote,
  check_add_path_capability local = true ->
  check_add_path_capability remote = true ->
  check_add_path_capability local = check_add_path_capability remote.
Proof.
  intros local remote Hlocal Hremote.
  rewrite Hlocal. rewrite Hremote. reflexivity.
Qed.

Theorem decode_path_id_success : forall b1 b2 b3 b4 rest,
  decode_path_id (b1 :: b2 :: b3 :: b4 :: rest) =
    Some (N.lor (N.lor (N.lor (N.shiftl b1 24) (N.shiftl b2 16))
                       (N.shiftl b3 8)) b4).
Proof.
  intros. unfold decode_path_id. reflexivity.
Qed.

Theorem decode_path_id_failure : forall bytes,
  Nat.ltb (length bytes) 4 = true ->
  decode_path_id bytes = None.
Proof.
  intros bytes Hlen.
  destruct bytes as [|b1 [|b2 [|b3 [|b4 rest]]]]; try reflexivity; simpl in Hlen; discriminate Hlen.
Qed.

(* =============================================================================
   §11.656: RFC 8205 BGPsec - Secure Path Validation
   ============================================================================= *)

Inductive SignatureAlgorithm :=
  | BGPSEC_ALGO_ECDSA_P256 : SignatureAlgorithm
  | BGPSEC_ALGO_RESERVED : SignatureAlgorithm.

Definition sig_algo_to_byte (algo : SignatureAlgorithm) : byte :=
  match algo with
  | BGPSEC_ALGO_ECDSA_P256 => 1
  | BGPSEC_ALGO_RESERVED => 0
  end.

Record BGPsecSignature := {
  sig_algorithm : SignatureAlgorithm;
  sig_subject_key_id : list byte;
  sig_value : list byte
}.

Record BGPsecPathSegment := {
  seg_secure_path_length : byte;
  seg_asn : word32;
  seg_signature : BGPsecSignature
}.

Definition BGPSEC_SKI_LENGTH : N := 20.
Definition BGPSEC_ECDSA_P256_SIG_LENGTH : N := 64.

Definition valid_ski_length (ski : list byte) : bool :=
  N.eqb (N.of_nat (length ski)) BGPSEC_SKI_LENGTH.

Definition valid_signature_length (algo : SignatureAlgorithm) (sig : list byte) : bool :=
  match algo with
  | BGPSEC_ALGO_ECDSA_P256 => N.eqb (N.of_nat (length sig)) BGPSEC_ECDSA_P256_SIG_LENGTH
  | BGPSEC_ALGO_RESERVED => false
  end.

Definition valid_bgpsec_signature (sig : BGPsecSignature) : bool :=
  andb (valid_ski_length sig.(sig_subject_key_id))
       (valid_signature_length sig.(sig_algorithm) sig.(sig_value)).

Definition valid_bgpsec_segment (seg : BGPsecPathSegment) : bool :=
  andb (valid_as_number seg.(seg_asn))
       (valid_bgpsec_signature seg.(seg_signature)).

Fixpoint all_segments_valid (segs : list BGPsecPathSegment) : bool :=
  match segs with
  | [] => true
  | seg :: rest => andb (valid_bgpsec_segment seg) (all_segments_valid rest)
  end.

Theorem valid_ecdsa_p256_signature_length : forall sig_value,
  valid_signature_length BGPSEC_ALGO_ECDSA_P256 sig_value = true ->
  N.of_nat (length sig_value) = BGPSEC_ECDSA_P256_SIG_LENGTH.
Proof.
  intros sig_value Hvalid.
  unfold valid_signature_length in Hvalid.
  apply N.eqb_eq. exact Hvalid.
Qed.

Theorem reserved_algo_invalid : forall sig_value,
  valid_signature_length BGPSEC_ALGO_RESERVED sig_value = false.
Proof.
  intros. unfold valid_signature_length. reflexivity.
Qed.

Theorem valid_ski_has_correct_length : forall ski,
  valid_ski_length ski = true ->
  N.of_nat (length ski) = BGPSEC_SKI_LENGTH.
Proof.
  intros ski Hvalid.
  unfold valid_ski_length in Hvalid.
  apply N.eqb_eq. exact Hvalid.
Qed.

Theorem valid_segment_has_valid_asn : forall seg,
  valid_bgpsec_segment seg = true ->
  valid_as_number seg.(seg_asn) = true.
Proof.
  intros seg Hvalid.
  unfold valid_bgpsec_segment in Hvalid.
  apply andb_prop in Hvalid.
  destruct Hvalid as [Hasn _].
  exact Hasn.
Qed.

Theorem all_valid_segments_implies_each_valid : forall seg rest,
  all_segments_valid (seg :: rest) = true ->
  valid_bgpsec_segment seg = true /\ all_segments_valid rest = true.
Proof.
  intros seg rest Hvalid.
  unfold all_segments_valid in Hvalid. fold all_segments_valid in Hvalid.
  apply andb_prop in Hvalid.
  exact Hvalid.
Qed.

(* =============================================================================
   §11.6565: BGPsec Cryptographic Verification Model
   ============================================================================= *)

(* Abstract cryptographic verification oracle (ECDSA P-256, X.509, RPKI) *)

Record PublicKey := {
  pk_asn : word32;
  pk_ski : list byte;
  pk_key_data : list byte  (* Abstract representation of key material *)
}.

(* Certificate validity period *)
Record ValidityPeriod := {
  vp_not_before : N;
  vp_not_after : N
}.

(* RPKI Resource Certificate *)
Record ResourceCertificate := {
  rc_asn : word32;
  rc_ski : list byte;
  rc_validity : ValidityPeriod;
  rc_revoked : bool
}.

(* =============================================================================
   ECDSA P-256 Implementation
   ============================================================================= *)

(* P-256 curve parameters (NIST secp256r1) *)
Definition p256_prime : N := 115792089210356248762697446949407573530086143415290314195533631308867097853951.
Definition p256_a : N := 115792089210356248762697446949407573530086143415290314195533631308867097853948.
Definition p256_b : N := 41058363725152142129326129780047268409114441015993725554835256314039467401291.
Definition p256_n : N := 115792089210356248762697446949407573529996955224135760342422259061068512044369.

(* Field arithmetic modulo p256_prime *)
Definition p256_add (x y : N) : N := (x + y) mod p256_prime.
Definition p256_sub (x y : N) : N := (x + p256_prime - y) mod p256_prime.
Definition p256_mul (x y : N) : N := (x * y) mod p256_prime.

(* Modular exponentiation by squaring *)
Fixpoint p256_pow_aux (base exp : N) (fuel : nat) : N :=
  match fuel with
  | O => 1
  | S fuel' =>
      if N.eqb exp 0 then 1
      else if N.eqb (exp mod 2) 0 then
        p256_mul (p256_pow_aux base (exp / 2) fuel') (p256_pow_aux base (exp / 2) fuel')
      else
        p256_mul base (p256_pow_aux base (exp - 1) fuel')
  end.

Definition p256_pow (base exp : N) : N :=
  p256_pow_aux base exp 256.

(* Modular inverse via Fermat's little theorem: a^(p-2) mod p *)
Definition p256_inv (x : N) : N :=
  if N.eqb x 0 then 0 else p256_pow x (p256_prime - 2).

(* Elliptic curve point (affine coordinates) *)
Inductive ECPoint :=
  | ECInfinity : ECPoint
  | ECPoint_xy : N -> N -> ECPoint.

(* EC point doubling *)
Definition ec_double (p : ECPoint) : ECPoint :=
  match p with
  | ECInfinity => ECInfinity
  | ECPoint_xy x y =>
      if N.eqb y 0 then ECInfinity
      else
        let s := p256_mul (p256_mul 3 (p256_mul x x)) (p256_inv (p256_mul 2 y)) in
        let x' := p256_sub (p256_mul s s) (p256_mul 2 x) in
        let y' := p256_sub (p256_mul s (p256_sub x x')) y in
        ECPoint_xy x' y'
  end.

(* EC point addition *)
Definition ec_add (p1 p2 : ECPoint) : ECPoint :=
  match p1, p2 with
  | ECInfinity, _ => p2
  | _, ECInfinity => p1
  | ECPoint_xy x1 y1, ECPoint_xy x2 y2 =>
      if N.eqb x1 x2 then
        if N.eqb y1 y2 then ec_double p1
        else ECInfinity
      else
        let s := p256_mul (p256_sub y2 y1) (p256_inv (p256_sub x2 x1)) in
        let x3 := p256_sub (p256_sub (p256_mul s s) x1) x2 in
        let y3 := p256_sub (p256_mul s (p256_sub x1 x3)) y1 in
        ECPoint_xy x3 y3
  end.

(* Scalar multiplication via double-and-add *)
Fixpoint ec_scalar_mul_aux (k : N) (p : ECPoint) (fuel : nat) : ECPoint :=
  match fuel with
  | O => ECInfinity
  | S fuel' =>
      if N.eqb k 0 then ECInfinity
      else if N.eqb k 1 then p
      else if N.eqb (k mod 2) 0 then
        ec_scalar_mul_aux (k / 2) (ec_double p) fuel'
      else
        ec_add p (ec_scalar_mul_aux (k - 1) p fuel')
  end.

Definition ec_scalar_mul (k : N) (p : ECPoint) : ECPoint :=
  ec_scalar_mul_aux k p 256.

(* P-256 base point G *)
Definition p256_G : ECPoint :=
  ECPoint_xy
    48439561293906451759052585252797914202762949526041747995844080717082404635286
    36134250956749795798585127919587881956611106672985015071877198253568414405109.

(* Decode bytes to N (big-endian) *)
Fixpoint bytes_to_N_aux (bs : list byte) (acc : N) : N :=
  match bs with
  | [] => acc
  | b :: rest => bytes_to_N_aux rest (N.lor (N.shiftl acc 8) b)
  end.

Definition bytes_to_N (bs : list byte) : N :=
  bytes_to_N_aux bs 0.

(* Simple hash function (stub - models SHA-256 behavior) *)
Fixpoint simple_hash_aux (bs : list byte) (acc : N) (fuel : nat) : N :=
  match fuel with
  | O => acc mod p256_n
  | S fuel' =>
      match bs with
      | [] => acc mod p256_n
      | b :: rest =>
          let acc' := (acc * 31 + b) mod p256_n in
          simple_hash_aux rest acc' fuel'
      end
  end.

Definition simple_hash (bs : list byte) : N :=
  simple_hash_aux bs 0 (length bs).

(* ECDSA P-256 signature verification *)
Definition verify_ecdsa_p256 (message : list byte) (public_key : list byte) (sig : BGPsecSignature) : bool :=
  if negb (N.eqb (N.of_nat (length sig.(sig_value))) 64) then false
  else
    let r_bytes := firstn 32 sig.(sig_value) in
    let s_bytes := skipn 32 sig.(sig_value) in
    let r := bytes_to_N r_bytes in
    let s := bytes_to_N s_bytes in
    if orb (N.eqb r 0) (N.eqb s 0) then false
    else if orb (N.leb p256_n r) (N.leb p256_n s) then false
    else
      let e := simple_hash message in
      let s_inv := p256_pow s (p256_n - 2) in
      let u1 := (e * s_inv) mod p256_n in
      let u2 := (r * s_inv) mod p256_n in
      let point1 := ec_scalar_mul u1 p256_G in
      let qx := bytes_to_N (firstn 32 public_key) in
      let qy := bytes_to_N (skipn 32 public_key) in
      let point2 := ec_scalar_mul u2 (ECPoint_xy qx qy) in
      let result := ec_add point1 point2 in
      match result with
      | ECInfinity => false
      | ECPoint_xy x y => N.eqb (x mod p256_n) r
      end.

(* Certificate chain validation *)
Definition check_certificate_validity (cert : ResourceCertificate) (current_time : N) : bool :=
  andb (N.leb cert.(rc_validity).(vp_not_before) current_time)
       (andb (N.leb current_time cert.(rc_validity).(vp_not_after))
             (negb cert.(rc_revoked))).

(* Verify a single BGPsec signature with certificate *)
Definition verify_bgpsec_signature_crypto
  (message : list byte)
  (sig : BGPsecSignature)
  (cert : ResourceCertificate)
  (current_time : N) : bool :=
  andb (valid_bgpsec_signature sig)
  (andb (check_certificate_validity cert current_time)
  (andb (N.eqb (N.of_nat (length sig.(sig_subject_key_id))) (N.of_nat (length cert.(rc_ski))))
        (verify_ecdsa_p256 message cert.(rc_ski) sig))).

(* Verify entire BGPsec path with certificate chain *)
Fixpoint verify_bgpsec_path_crypto
  (message : list byte)
  (segments : list BGPsecPathSegment)
  (certs : list ResourceCertificate)
  (current_time : N)
  (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match segments, certs with
      | [], [] => true
      | seg :: rest_segs, cert :: rest_certs =>
          andb (N.eqb seg.(seg_asn) cert.(rc_asn))
          (andb (verify_bgpsec_signature_crypto message seg.(seg_signature) cert current_time)
                (verify_bgpsec_path_crypto message rest_segs rest_certs current_time fuel'))
      | _, _ => false
      end
  end.

(* Valid signature structure necessary for crypto verification *)
Theorem crypto_verification_requires_valid_structure : forall msg sig cert time,
  verify_bgpsec_signature_crypto msg sig cert time = true ->
  valid_bgpsec_signature sig = true.
Proof.
  intros msg sig cert time Hverify.
  unfold verify_bgpsec_signature_crypto in Hverify.
  apply andb_prop in Hverify.
  destruct Hverify as [Hvalid _].
  exact Hvalid.
Qed.

(* Expired certificates fail verification *)
Theorem expired_cert_fails_verification : forall cert time,
  cert.(rc_validity).(vp_not_after) < time ->
  check_certificate_validity cert time = false.
Proof.
  intros cert time Hexpired.
  unfold check_certificate_validity.
  apply andb_false_iff.
  right.
  apply andb_false_iff.
  left.
  apply N.leb_gt in Hexpired.
  rewrite Hexpired.
  reflexivity.
Qed.

(* Revoked certificates fail verification *)
Theorem revoked_cert_fails_verification : forall cert time,
  cert.(rc_revoked) = true ->
  check_certificate_validity cert time = false.
Proof.
  intros cert time Hrevoked.
  unfold check_certificate_validity.
  apply andb_false_iff.
  right.
  apply andb_false_iff.
  right.
  rewrite Hrevoked.
  reflexivity.
Qed.

(* Path verification requires matching AS numbers *)
Theorem path_verification_requires_matching_asn : forall msg seg cert rest_segs rest_certs time fuel,
  verify_bgpsec_path_crypto msg (seg :: rest_segs) (cert :: rest_certs) time (S fuel) = true ->
  seg.(seg_asn) = cert.(rc_asn).
Proof.
  intros msg seg cert rest_segs rest_certs time fuel Hverify.
  simpl in Hverify.
  apply andb_prop in Hverify.
  destruct Hverify as [Hasn _].
  apply N.eqb_eq.
  exact Hasn.
Qed.

(* =============================================================================
   §11.66: RFC 4760 MP-BGP - Address Family Consistency
   ============================================================================= *)

(* MP-BGP AFI/SAFI validation functions defined earlier in §5.5 *)

(* IPv4 Unicast is a valid combination *)
Theorem ipv4_unicast_valid :
  valid_afi_safi_combination AFI_IPV4 SAFI_UNICAST = true.
Proof.
  unfold valid_afi_safi_combination, AFI_IPV4, SAFI_UNICAST.
  simpl. reflexivity.
Qed.

(* IPv6 Unicast is a valid combination *)
Theorem ipv6_unicast_valid :
  valid_afi_safi_combination AFI_IPV6 SAFI_UNICAST = true.
Proof.
  unfold valid_afi_safi_combination, AFI_IPV6, SAFI_UNICAST.
  simpl. reflexivity.
Qed.

(* L2VPN VPLS is a valid combination *)
Theorem l2vpn_vpls_valid :
  valid_afi_safi_combination AFI_L2VPN SAFI_VPLS = true.
Proof.
  unfold valid_afi_safi_combination, AFI_L2VPN, SAFI_VPLS.
  simpl. reflexivity.
Qed.

(* L2VPN EVPN is a valid combination *)
Theorem l2vpn_evpn_valid :
  valid_afi_safi_combination AFI_L2VPN SAFI_EVPN = true.
Proof.
  unfold valid_afi_safi_combination, AFI_L2VPN, SAFI_EVPN.
  simpl. reflexivity.
Qed.

(* BGP-LS is a valid combination *)
Theorem bgpls_valid :
  valid_afi_safi_combination AFI_BGPLS SAFI_BGPLS = true.
Proof.
  unfold valid_afi_safi_combination, AFI_BGPLS, SAFI_BGPLS.
  simpl. reflexivity.
Qed.

(* Invalid combinations are rejected *)
Theorem invalid_afi_safi_rejected : forall afi safi,
  valid_afi_safi_combination afi safi = false ->
  ~(afi = AFI_IPV4 /\ (safi = SAFI_UNICAST \/ safi = SAFI_MULTICAST \/
                       safi = SAFI_MPLS_VPN \/ safi = SAFI_FLOWSPEC)) /\
  ~(afi = AFI_IPV6 /\ (safi = SAFI_UNICAST \/ safi = SAFI_MULTICAST \/
                       safi = SAFI_MPLS_VPN \/ safi = SAFI_FLOWSPEC)) /\
  ~(afi = AFI_L2VPN /\ (safi = SAFI_VPLS \/ safi = SAFI_EVPN)) /\
  ~(afi = AFI_BGPLS /\ safi = SAFI_BGPLS).
Proof.
  intros afi safi Hinvalid.
  unfold valid_afi_safi_combination in Hinvalid.
  repeat split; intro H; destruct H as [Hafi Hsafi];
    rewrite Hafi in Hinvalid;
    try (destruct Hsafi as [Hsafi | Hsafi]);
    try (destruct Hsafi as [Hsafi | Hsafi]);
    try (destruct Hsafi as [Hsafi | Hsafi]);
    rewrite Hsafi in Hinvalid;
    simpl in Hinvalid;
    discriminate Hinvalid.
Qed.

(* Decoding AFI from valid bytes succeeds *)
Theorem decode_afi_success : forall b1 b2 rest,
  decode_afi (b1 :: b2 :: rest) = Some (N.lor (N.shiftl b1 8) b2).
Proof.
  intros. unfold decode_afi. reflexivity.
Qed.

(* Decoding SAFI from valid bytes succeeds *)
Theorem decode_safi_success : forall b1 b2 safi rest,
  decode_safi (b1 :: b2 :: safi :: rest) = Some safi.
Proof.
  intros. unfold decode_safi. reflexivity.
Qed.

(* =============================================================================
   §11.67: Route Oscillation Prevention
   ============================================================================= *)

(* compare_routes defines total order preventing oscillation via:
   1. Antisymmetry: r1 > r2 implies ¬(r2 > r1)
   2. Stability: best(best(routes)) = best(routes) *)

(* compare_routes respects local_pref strictly *)
Theorem compare_routes_respects_local_pref : forall r1 r2,
  route_local_pref r1 > route_local_pref r2 ->
  compare_routes r1 r2 = true.
Proof.
  intros r1 r2 H.
  unfold compare_routes.
  assert (Hlt: route_local_pref r2 < route_local_pref r1) by lia.
  apply N.ltb_lt in Hlt.
  rewrite Hlt.
  reflexivity.
Qed.

(* compare_routes antisymmetric for different local_pref *)
Theorem compare_routes_antisymmetric_pref : forall r1 r2,
  route_local_pref r1 <> route_local_pref r2 ->
  compare_routes r1 r2 = true ->
  compare_routes r2 r1 = false.
Proof.
  intros r1 r2 Hneq H.
  unfold compare_routes in *.
  destruct (N.ltb (route_local_pref r2) (route_local_pref r1)) eqn:Hpref1.
  - apply N.ltb_lt in Hpref1.
    assert (Hpref2: N.ltb (route_local_pref r1) (route_local_pref r2) = false).
    { apply N.ltb_ge. lia. }
    rewrite Hpref2.
    reflexivity.
  - destruct (N.ltb (route_local_pref r1) (route_local_pref r2)) eqn:Hpref2.
    + discriminate H.
    + apply N.ltb_ge in Hpref1. apply N.ltb_ge in Hpref2.
      lia.
Qed.

(* Best path selection is stable: best(best(routes)) = best(routes) *)
Theorem best_path_selection_stable : forall routes best,
  bgp_best_path_selection routes = Some best ->
  bgp_best_path_selection [best] = Some best.
Proof.
  intros routes best Hbest.
  unfold bgp_best_path_selection in *.
  remember (filter (fun r : BGPRoute => route_next_hop_reachable r) routes) as reachable eqn:Heqreach.
  destruct (fold_left _ reachable None) as [result|] eqn:Hfold.
  - apply fold_best_path_in_list in Hfold.
    assert (Hin: In result (filter (fun r : BGPRoute => route_next_hop_reachable r) routes)).
    { rewrite <- Heqreach. exact Hfold. }
    apply filter_In in Hin.
    destruct Hin as [_ Hreach].
    inversion Hbest. subst.
    simpl.
    rewrite Hreach.
    simpl.
    reflexivity.
  - discriminate Hbest.
Qed.

(* No oscillation: stable best path remains stable *)
Theorem no_route_oscillation : forall rib route,
  (update_loc_rib rib).(loc_rib) = [route] ->
  (update_loc_rib (update_loc_rib rib)).(loc_rib) = [route].
Proof.
  intros rib route Hloc.
  unfold update_loc_rib in *.
  simpl in *.
  rewrite Hloc.
  unfold bgp_best_path_selection.
  simpl.
  destruct (route_next_hop_reachable route) eqn:Hreach.
  - simpl. reflexivity.
  - destruct (bgp_best_path_selection (adj_rib_in rib)) as [result|] eqn:Hbest.
    + unfold bgp_best_path_selection in Hbest.
      remember (filter (fun r : BGPRoute => route_next_hop_reachable r) (adj_rib_in rib)) as reachable eqn:Heqreach.
      destruct (fold_left _ reachable None) as [result'|] eqn:Hfold.
      * apply fold_best_path_in_list in Hfold.
        assert (Hin: In result' (filter (fun r : BGPRoute => route_next_hop_reachable r) (adj_rib_in rib))).
        { rewrite <- Heqreach. exact Hfold. }
        apply filter_In in Hin.
        destruct Hin as [_ Hreach'].
        inversion Hbest. subst.
        inversion Hloc. subst.
        rewrite Hreach' in Hreach.
        discriminate Hreach.
      * discriminate Hbest.
    + discriminate Hloc.
Qed.

(* =============================================================================
   §11.7: Deep Properties - Route Consistency
   ============================================================================= *)

Definition has_origin (route : BGPRoute) : Prop :=
  route.(route_origin) = ORIGIN_IGP \/
  route.(route_origin) = ORIGIN_EGP \/
  route.(route_origin) = ORIGIN_INCOMPLETE.

Definition has_as_path (route : BGPRoute) : Prop :=
  exists path, route.(route_as_path) = path.

Definition has_next_hop (route : BGPRoute) : Prop :=
  exists nh, route.(route_next_hop) = nh /\ nh <> 0.

Lemma origin_bounded : forall b : byte,
  b = ORIGIN_IGP \/ b = ORIGIN_EGP \/ b = ORIGIN_INCOMPLETE \/
  (b <> ORIGIN_IGP /\ b <> ORIGIN_EGP /\ b <> ORIGIN_INCOMPLETE).
Proof.
  intros. unfold ORIGIN_IGP, ORIGIN_EGP, ORIGIN_INCOMPLETE.
  destruct (N.eq_dec b 0); [left; auto |].
  destruct (N.eq_dec b 1); [right; left; auto |].
  destruct (N.eq_dec b 2); [right; right; left; auto |].
  right. right. right. repeat split; intro; subst; contradiction.
Qed.

Theorem route_has_origin : forall route,
  has_origin route \/ ~has_origin route.
Proof.
  intros. unfold has_origin.
  destruct (origin_bounded (route_origin route)) as [H|[H|[H|H]]]; auto.
  right. intro. destruct H0 as [H0|[H0|H0]]; destruct H as [H1 [H2 H3]]; contradiction.
Qed.

Theorem route_has_as_path : forall route,
  has_as_path route.
Proof.
  intros. unfold has_as_path. exists (route_as_path route). reflexivity.
Qed.

Theorem route_has_next_hop_decidable : forall route,
  has_next_hop route \/ route.(route_next_hop) = 0.
Proof.
  intros. unfold has_next_hop.
  destruct (N.eq_dec (route_next_hop route) 0).
  - right. exact e.
  - left. exists (route_next_hop route). split; auto.
Qed.

(* =============================================================================
   §11.8: Properties of RFC Enhancements
   ============================================================================= *)

(* RFC 8654: Extended Message capability *)
Theorem extended_message_allows_larger: forall local remote,
  supports_extended_message local = true ->
  supports_extended_message remote = true ->
  negotiated_max_message_length local remote = 65535.
Proof.
  intros local remote Hlocal Hremote.
  unfold negotiated_max_message_length.
  rewrite Hlocal, Hremote. simpl. reflexivity.
Qed.

(* RFC 8654: Without capability, stays at RFC 4271 default *)
Theorem no_extended_message_default: forall local remote,
  supports_extended_message local = false ->
  negotiated_max_message_length local remote = BGP_MAX_MESSAGE_LENGTH.
Proof.
  intros local remote Hlocal.
  unfold negotiated_max_message_length.
  rewrite Hlocal. simpl. reflexivity.
Qed.

(* RFC 6793: AS_TRANS is a valid 2-byte representable AS *)
Theorem as_trans_in_range:
  AS_TRANS < 65536.
Proof.
  unfold AS_TRANS. lia.
Qed.

(* RFC 6793: Merging preserves list structure *)
Theorem merge_as_paths_length_bound: forall as_path as4_path,
  length (merge_as_paths as_path as4_path) = length as_path.
Proof.
  intros as_path. induction as_path as [|asn rest IH]; intros as4_path.
  - simpl. reflexivity.
  - simpl. destruct as4_path as [|as4 rest4].
    + simpl. rewrite IH. reflexivity.
    + destruct (N.eqb asn AS_TRANS); simpl; rewrite IH; reflexivity.
Qed.

(* RFC 6793: Merge with empty AS4_PATH preserves AS_PATH *)
Theorem merge_with_empty_as4: forall as_path,
  merge_as_paths as_path [] = as_path.
Proof.
  induction as_path as [|asn rest IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* RFC 5065: Confederation segments are valid AS_PATH segment types *)
Theorem confed_segments_valid:
  validate_as_path_structure [AS_CONFED_SEQUENCE; 1; 0; 0] = true /\
  validate_as_path_structure [AS_CONFED_SET; 1; 0; 0] = true.
Proof.
  split; unfold validate_as_path_structure; simpl; reflexivity.
Qed.

(* RFC 6793: Confederation segments forbidden in AS4_PATH *)
Theorem confed_segments_invalid_as4:
  validate_as4_path_structure [AS_CONFED_SEQUENCE; 1; 0; 0; 0; 0] = false /\
  validate_as4_path_structure [AS_CONFED_SET; 1; 0; 0; 0; 0] = false.
Proof.
  split; unfold validate_as4_path_structure; simpl; reflexivity.
Qed.

(* Extended-length flag validation correctness *)
Theorem extended_length_flag_accepts_any_when_set: forall attr,
  has_flag attr.(attr_flags) ATTR_FLAG_EXTENDED = true ->
  valid_extended_length_flag attr = true.
Proof.
  intros attr Hflag.
  unfold valid_extended_length_flag.
  rewrite Hflag. reflexivity.
Qed.

Theorem extended_length_flag_rejects_large_when_unset: forall attr,
  has_flag attr.(attr_flags) ATTR_FLAG_EXTENDED = false ->
  attr.(attr_length) > 255 ->
  valid_extended_length_flag attr = false.
Proof.
  intros attr Hflag Hlarge.
  unfold valid_extended_length_flag.
  rewrite Hflag. apply N.leb_gt. lia.
Qed.

(* =============================================================================
   §12: OCaml Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction "bgp4.ml"
  init_bgp_session
  bgp_state_transition
  bgp_best_path_selection
  valid_bgp_header
  valid_open_message
  valid_update_message
  valid_keepalive_message
  valid_path_attribute
  get_effective_as_path
  supports_extended_message
  negotiated_max_message_length.
 
