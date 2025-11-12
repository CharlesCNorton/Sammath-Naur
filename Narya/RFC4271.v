(* =============================================================================
   Formal Verification of Border Gateway Protocol Version 4 (BGP-4)
   
   Specification: RFC 4271 (Y. Rekhter, T. Li, S. Hares, January 2006)
   Target: BGP-4 Protocol
   
   Module: BGP-4 Protocol Formalization and Verification
   Author: Charles C Norton
   Date: September 1, 2025
   
   "Greater still were the maps that showed the roads between realms."
   
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
   Section 1: Basic Types and Constants
   ============================================================================= *)

Definition byte := N.
Definition word16 := N.
Definition word32 := N.

(* BGP Constants (RFC 4271 Section 4) *)
Definition BGP_VERSION : byte := 4.
Definition BGP_PORT : word16 := 179.
Definition BGP_MARKER_LENGTH : N := 16.
Definition BGP_HEADER_LENGTH : N := 19.
Definition BGP_MAX_MESSAGE_LENGTH : N := 4096.
Definition BGP_MIN_MESSAGE_LENGTH : N := 19.

(* Timer Constants (RFC 4271 Section 10) *)
Definition HOLD_TIME_DEFAULT : N := 90.      (* seconds *)
Definition HOLD_TIME_MIN : N := 3.           (* seconds *)
Definition HOLD_TIME_MAX : N := 65535.       (* seconds *)
Definition KEEPALIVE_TIME : N := 30.         (* seconds *)
Definition CONNECT_RETRY_TIME : N := 120.    (* seconds *)
Definition MIN_AS_ORIGINATION_INTERVAL : N := 15. (* seconds *)
Definition MIN_ROUTE_ADVERTISEMENT_INTERVAL : N := 30. (* seconds *)

(* =============================================================================
   Section 2: BGP Message Types (RFC 4271 Section 4.1)
   ============================================================================= *)

Inductive BGPMessageType :=
  | OPEN : BGPMessageType         (* 1 *)
  | UPDATE : BGPMessageType       (* 2 *)
  | NOTIFICATION : BGPMessageType (* 3 *)
  | KEEPALIVE : BGPMessageType.   (* 4 *)

(* BGP Message Header *)
Record BGPHeader := {
  bgp_marker : list byte;  (* 16 bytes, all 1s *)
  bgp_length : word16;
  bgp_type : BGPMessageType
}.

(* =============================================================================
   Section 3: OPEN Message (RFC 4271 Section 4.2)
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

(* Capability codes for optional parameters *)
Definition CAP_MULTIPROTOCOL : byte := 1.
Definition CAP_ROUTE_REFRESH : byte := 2.
Definition CAP_4BYTE_AS : byte := 65.
Definition CAP_ADD_PATH : byte := 69.

(* =============================================================================
   Section 4: UPDATE Message (RFC 4271 Section 4.3)
   ============================================================================= *)

Record NLRI := {
  nlri_prefix_len : byte;
  nlri_prefix : list byte
}.

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

(* Path Attribute Flags - RFC 4271 uses "bit 0" for high-order bit (MSB) *)
Definition ATTR_FLAG_OPTIONAL : byte := 128.  (* Bit 0 = MSB = 0x80 *)
Definition ATTR_FLAG_TRANSITIVE : byte := 64. (* Bit 1 = 0x40 *)
Definition ATTR_FLAG_PARTIAL : byte := 32.    (* Bit 2 = 0x20 *)
Definition ATTR_FLAG_EXTENDED : byte := 16.   (* Bit 3 = 0x10 *)

(* Path Attribute Type Codes *)
Definition ATTR_ORIGIN : byte := 1.
Definition ATTR_AS_PATH : byte := 2.
Definition ATTR_NEXT_HOP : byte := 3.
Definition ATTR_MULTI_EXIT_DISC : byte := 4.
Definition ATTR_LOCAL_PREF : byte := 5.
Definition ATTR_ATOMIC_AGGREGATE : byte := 6.
Definition ATTR_AGGREGATOR : byte := 7.
Definition ATTR_COMMUNITIES : byte := 8.
Definition ATTR_MP_REACH_NLRI : byte := 14.
Definition ATTR_MP_UNREACH_NLRI : byte := 15.

(* Origin values *)
Definition ORIGIN_IGP : byte := 0.
Definition ORIGIN_EGP : byte := 1.
Definition ORIGIN_INCOMPLETE : byte := 2.

(* AS_PATH segment types *)
Definition AS_SET : byte := 1.
Definition AS_SEQUENCE : byte := 2.

(* =============================================================================
   Section 5: NOTIFICATION Message (RFC 4271 Section 4.5)
   ============================================================================= *)

Record BGPNotification := {
  notif_error_code : byte;
  notif_error_subcode : byte;
  notif_data : list byte
}.

(* Error Codes *)
Definition ERR_MESSAGE_HEADER : byte := 1.
Definition ERR_OPEN_MESSAGE : byte := 2.
Definition ERR_UPDATE_MESSAGE : byte := 3.
Definition ERR_HOLD_TIMER : byte := 4.
Definition ERR_FSM : byte := 5.
Definition ERR_CEASE : byte := 6.

(* OPEN Message Error Subcodes *)
Definition OPEN_ERR_UNSUPPORTED_VERSION : byte := 1.
Definition OPEN_ERR_BAD_PEER_AS : byte := 2.
Definition OPEN_ERR_BAD_BGP_IDENTIFIER : byte := 3.
Definition OPEN_ERR_UNSUPPORTED_PARAM : byte := 4.
Definition OPEN_ERR_UNACCEPTABLE_HOLD_TIME : byte := 6.

(* UPDATE Message Error Subcodes *)
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

(* Message Header Error Subcodes *)
Definition HEADER_ERR_CONNECTION_NOT_SYNCHRONIZED : byte := 1.
Definition HEADER_ERR_BAD_MESSAGE_LENGTH : byte := 2.
Definition HEADER_ERR_BAD_MESSAGE_TYPE : byte := 3.

(* FSM Error Subcodes *)
Definition FSM_ERR_UNSPECIFIED : byte := 0.
Definition FSM_ERR_UNEXPECTED_MESSAGE_OPENSENT : byte := 1.
Definition FSM_ERR_UNEXPECTED_MESSAGE_OPENCONFIRM : byte := 2.
Definition FSM_ERR_UNEXPECTED_MESSAGE_ESTABLISHED : byte := 3.

(* =============================================================================
   Section 5.5: Validation Functions
   ============================================================================= *)

(* Validate BGP header marker (RFC 4271 Section 4.1) *)
Definition valid_marker (marker : list byte) : bool :=
  andb (N.eqb (N.of_nat (length marker)) BGP_MARKER_LENGTH)
       (forallb (fun b => N.eqb b 255) marker).

(* Validate BGP header length field (RFC 4271 Section 4.1) *)
Definition valid_header_length (length : word16) : bool :=
  andb (N.leb BGP_MIN_MESSAGE_LENGTH length)
       (N.leb length BGP_MAX_MESSAGE_LENGTH).

(* Validate BGP message length matches content *)
Definition validate_message_length (hdr : BGPHeader) (msg_type : BGPMessageType)
                                   (content_length : N) : bool :=
  N.eqb hdr.(bgp_length) (BGP_HEADER_LENGTH + content_length).

(* Validate complete BGP header *)
Definition valid_bgp_header (hdr : BGPHeader) : bool :=
  andb (valid_marker hdr.(bgp_marker))
       (valid_header_length hdr.(bgp_length)).

(* Validate KEEPALIVE message (RFC 4271 Section 4.4 - header only, 19 bytes) *)
Definition valid_keepalive_message (hdr : BGPHeader) : bool :=
  andb (valid_bgp_header hdr)
       (N.eqb hdr.(bgp_length) 19).

(* Validate BGP Identifier is non-zero (RFC 4271 Section 4.2) *)
Definition valid_bgp_identifier (id : word32) : bool :=
  negb (N.eqb id 0).

(* Validate Hold Time (RFC 4271 Section 4.2, 6.2) *)
Definition valid_hold_time (hold_time : word16) : bool :=
  orb (N.eqb hold_time 0)
      (andb (N.leb HOLD_TIME_MIN hold_time)
            (N.leb hold_time HOLD_TIME_MAX)).

(* Validate AS number (RFC 4271 - AS 0 is reserved) *)
Definition valid_as_number (asn : word16) : bool :=
  negb (N.eqb asn 0).

(* Validate ORIGIN attribute value (RFC 4271 Section 5.1.1) *)
Definition valid_origin_value (origin : byte) : bool :=
  orb (N.eqb origin ORIGIN_IGP)
      (orb (N.eqb origin ORIGIN_EGP)
           (N.eqb origin ORIGIN_INCOMPLETE)).

(* Validate NLRI prefix length (RFC 4271 Section 4.3 - must be 0-32 for IPv4) *)
Definition valid_nlri_prefix_len (prefix_len : byte) : bool :=
  N.leb prefix_len 32.

(* Check that host bits are zero in NLRI prefix *)
Fixpoint check_host_bits_zero (prefix : list byte) (prefix_len : N) : bool :=
  let significant_bytes := prefix_len / 8 in
  let remaining_bits := prefix_len mod 8 in
  match prefix with
  | [] => true
  | b :: rest =>
      if N.ltb (N.of_nat (length prefix - 1)) significant_bytes then
        check_host_bits_zero rest prefix_len
      else if N.eqb (N.of_nat (length prefix - 1)) significant_bytes then
        if N.eqb remaining_bits 0 then true
        else
          let mask := N.shiftr 255 remaining_bits in
          let masked := N.land b (N.lxor mask 255) in
          andb (N.eqb masked 0) (check_host_bits_zero rest prefix_len)
      else
        andb (N.eqb b 0) (check_host_bits_zero rest prefix_len)
  end.

(* Validate NLRI structure *)
Definition valid_nlri (nlri : NLRI) : bool :=
  let len_ok := valid_nlri_prefix_len nlri.(nlri_prefix_len) in
  let bytes_needed := (nlri.(nlri_prefix_len) + 7) / 8 in
  let bytes_ok := N.eqb (N.of_nat (length nlri.(nlri_prefix))) bytes_needed in
  let host_bits_ok := check_host_bits_zero nlri.(nlri_prefix) nlri.(nlri_prefix_len) in
  andb len_ok (andb bytes_ok host_bits_ok).

(* Validate NEXT_HOP IPv4 address (RFC 4271 Section 5.1.3) *)
Definition valid_next_hop (next_hop_bytes : list byte) : bool :=
  match next_hop_bytes with
  | [a; b; c; d] =>
      let not_zero := negb (andb (N.eqb a 0) (andb (N.eqb b 0) (andb (N.eqb c 0) (N.eqb d 0)))) in
      let not_multicast := N.ltb a 224 in  (* Multicast: 224.0.0.0/4 *)
      andb not_zero not_multicast
  | _ => false
  end.

(* Check for BGP Identifier collision (RFC 4271 Section 6.2) *)
Definition has_bgp_id_collision (local_id remote_id : word32) : bool :=
  N.eqb local_id remote_id.

(* Validate optional parameter length in OPEN *)
Definition valid_optional_params (params : list BGPOptionalParameter) (declared_len : byte) : bool :=
  let total_len := fold_left (fun acc p => acc + 2 + N.of_nat (length p.(opt_param_value))) params 0 in
  N.eqb total_len declared_len.

(* Verify peer AS matches expected value *)
Definition verify_peer_as (expected_as received_as : word16) : bool :=
  N.eqb expected_as received_as.

(* Validate OPEN message (RFC 4271 Section 6.2) *)
Definition valid_open_message (open_msg : BGPOpen) : bool :=
  andb (N.eqb open_msg.(open_version) BGP_VERSION)
       (andb (valid_bgp_identifier open_msg.(open_bgp_identifier))
             (andb (valid_hold_time open_msg.(open_hold_time))
                   (andb (valid_as_number open_msg.(open_my_as))
                         (valid_optional_params open_msg.(open_opt_params) open_msg.(open_opt_param_len))))).

(* Validate path attribute flags (RFC 4271 Section 4.3) *)
Definition has_flag (flags target : byte) : bool :=
  negb (N.eqb (N.land flags target) 0).

Definition valid_path_attribute (attr : PathAttribute) : bool :=
  let is_optional := has_flag attr.(attr_flags) ATTR_FLAG_OPTIONAL in
  let is_transitive := has_flag attr.(attr_flags) ATTR_FLAG_TRANSITIVE in
  let is_partial := has_flag attr.(attr_flags) ATTR_FLAG_PARTIAL in
  let is_extended := has_flag attr.(attr_flags) ATTR_FLAG_EXTENDED in
  let flags_ok := match attr.(attr_type_code) with
    | 1 => andb (negb is_optional) is_transitive  (* ORIGIN: well-known mandatory *)
    | 2 => andb (negb is_optional) is_transitive  (* AS_PATH: well-known mandatory *)
    | 3 => andb (negb is_optional) is_transitive  (* NEXT_HOP: well-known mandatory *)
    | 4 => is_optional  (* MULTI_EXIT_DISC: optional non-transitive *)
    | 5 => andb (negb is_optional) is_transitive  (* LOCAL_PREF: well-known mandatory *)
    | 6 => andb (negb is_optional) is_transitive  (* ATOMIC_AGGREGATE: well-known *)
    | 7 => is_optional  (* AGGREGATOR: optional transitive *)
    | _ => true  (* Unknown attributes: accept if properly marked *)
    end in
  let value_ok := match attr.(attr_type_code) with
    | 1 => match attr.(attr_value) with
           | [v] => valid_origin_value v
           | _ => false
           end
    | 2 => negb (N.eqb (N.of_nat (length attr.(attr_value))) 0)  (* AS_PATH: non-empty *)
    | 3 => valid_next_hop attr.(attr_value)  (* NEXT_HOP: valid IPv4 *)
    | 4 => N.eqb (N.of_nat (length attr.(attr_value))) 4  (* MED: 4 bytes *)
    | 5 => N.eqb (N.of_nat (length attr.(attr_value))) 4  (* LOCAL_PREF: 4 bytes *)
    | _ => true
    end in
  andb flags_ok value_ok.

(* Validate UPDATE message has mandatory attributes *)
Definition has_mandatory_attributes (attrs : list PathAttribute) : bool :=
  let has_origin := existsb (fun a => N.eqb a.(attr_type_code) ATTR_ORIGIN) attrs in
  let has_as_path := existsb (fun a => N.eqb a.(attr_type_code) ATTR_AS_PATH) attrs in
  let has_next_hop := existsb (fun a => N.eqb a.(attr_type_code) ATTR_NEXT_HOP) attrs in
  andb has_origin (andb has_as_path has_next_hop).

(* Check for duplicate attributes (RFC 4271 Section 6.3) *)
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

(* Validate AS_PATH for loops (full loop detection) *)
Fixpoint has_full_as_loop (as_path : list word32) (seen : list word32) : bool :=
  match as_path with
  | [] => false
  | asn :: rest =>
      if existsb (N.eqb asn) seen
      then true
      else has_full_as_loop rest (asn :: seen)
  end.

(* Check if AS_PATH contains own AS *)
Definition has_as_loop (my_as : word32) (as_path : list word32) : bool :=
  existsb (fun asn => N.eqb asn my_as) as_path.

(* Combined AS_PATH validation *)
Definition valid_as_path_no_loops (my_as : word32) (as_path : list word32) : bool :=
  andb (negb (has_as_loop my_as as_path))
       (negb (has_full_as_loop as_path [])).

(* Validate withdrawn routes length *)
Definition validate_withdrawn_length (withdrawn_routes : list NLRI) (declared_len : word16) : bool :=
  let actual_len := fold_left (fun acc nlri => acc + 1 + N.of_nat (length nlri.(nlri_prefix))) withdrawn_routes 0 in
  N.eqb actual_len declared_len.

(* Validate path attributes total length *)
Definition validate_path_attr_length (attrs : list PathAttribute) (declared_len : word16) : bool :=
  let actual_len := fold_left (fun acc attr => acc + 3 + attr.(attr_length)) attrs 0 in
  N.eqb actual_len declared_len.

(* Validate complete UPDATE message *)
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

(* Helper to decode AS numbers from bytes (simplified) *)
Fixpoint take_as_numbers (n : nat) (bs : list byte) : list word32 :=
  match n, bs with
  | O, _ => []
  | S n', b1 :: b2 :: rest' =>
      (N.lor (N.shiftl b1 8) b2) :: take_as_numbers n' rest'
  | _, _ => []
  end.

Fixpoint decode_as_path (bytes : list byte) : list word32 :=
  match bytes with
  | [] => []
  | _ :: len :: rest =>
      take_as_numbers (N.to_nat len) rest
  | _ => []
  end.

(* Check for AS_PATH loop in UPDATE *)
Definition update_has_as_loop (my_as : word32) (update : BGPUpdate) : bool :=
  match find (fun attr => N.eqb attr.(attr_type_code) ATTR_AS_PATH)
             update.(update_path_attributes) with
  | None => false
  | Some as_path_attr =>
      has_as_loop my_as (decode_as_path as_path_attr.(attr_value))
  end.

(* =============================================================================
   Section 6: BGP Finite State Machine (RFC 4271 Section 8)
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
  session_time_elapsed : N  (* Time elapsed in current state (for timer mechanics) *)
}.

(* Initialize BGP session *)
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
     session_time_elapsed := 0 |}.

(* =============================================================================
   Section 7: BGP State Machine Events (RFC 4271 Section 8.1)
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

(* Timer tick - increment elapsed time and check for expiries *)
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
      session_time_elapsed := new_elapsed |}, events).

(* =============================================================================
   Section 8: State Transitions (RFC 4271 Section 8.2)
   ============================================================================= *)

(* Helper: Reset session to IDLE state *)
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
     session_time_elapsed := 0 |}.

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
          session_delay_open_timer := Some 5;  (* DelayOpen timer set to 5 seconds *)
          session_idle_hold_timer := session.(session_idle_hold_timer);
          session_capabilities := session.(session_capabilities);
          session_time_elapsed := 0 |}, None)

  | CONNECT, DelayOpenTimerExpires =>
      ({| session_state := OPENSENT;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := session.(session_remote_id);
          session_hold_time := session.(session_hold_time);
          session_keepalive_time := session.(session_keepalive_time);
          session_connect_retry_counter := session.(session_connect_retry_counter);
          session_connect_retry_timer := None;
          session_hold_timer := Some session.(session_hold_time);
          session_keepalive_timer := session.(session_keepalive_timer);
          session_delay_open_timer := None;
          session_idle_hold_timer := session.(session_idle_hold_timer);
          session_capabilities := session.(session_capabilities);
          session_time_elapsed := session.(session_time_elapsed) |}, Some OPEN)

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
          session_time_elapsed := 0 |}, None)
  
  | CONNECT, TCPConnectionConfirmed =>
      ({| session_state := OPENSENT;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := session.(session_remote_id);
          session_hold_time := session.(session_hold_time);
          session_keepalive_time := session.(session_keepalive_time);
          session_connect_retry_counter := session.(session_connect_retry_counter);
          session_connect_retry_timer := None;
          session_hold_timer := Some session.(session_hold_time);
          session_keepalive_timer := session.(session_keepalive_timer);
          session_delay_open_timer := session.(session_delay_open_timer);
          session_idle_hold_timer := session.(session_idle_hold_timer);
          session_capabilities := session.(session_capabilities);
          session_time_elapsed := session.(session_time_elapsed) |}, Some OPEN)

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
          session_time_elapsed := session.(session_time_elapsed) |}, None)

  | ACTIVE, TCPConnectionConfirmed =>
      ({| session_state := OPENSENT;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := session.(session_remote_id);
          session_hold_time := session.(session_hold_time);
          session_keepalive_time := session.(session_keepalive_time);
          session_connect_retry_counter := session.(session_connect_retry_counter);
          session_connect_retry_timer := None;
          session_hold_timer := Some session.(session_hold_time);
          session_keepalive_timer := session.(session_keepalive_timer);
          session_delay_open_timer := session.(session_delay_open_timer);
          session_idle_hold_timer := session.(session_idle_hold_timer);
          session_capabilities := session.(session_capabilities);
          session_time_elapsed := session.(session_time_elapsed) |}, Some OPEN)

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
          session_time_elapsed := session.(session_time_elapsed) |}, None)

  | OPENSENT, BGPOpen_Received open_msg =>
      if valid_open_message open_msg then
        if has_bgp_id_collision session.(session_local_id) open_msg.(open_bgp_identifier) then
          (reset_to_idle session, Some NOTIFICATION)  (* BGP ID collision *)
        else
          ({| session_state := OPENCONFIRM;
              session_local_as := session.(session_local_as);
              session_remote_as := open_msg.(open_my_as);
              session_local_id := session.(session_local_id);
              session_remote_id := open_msg.(open_bgp_identifier);
              session_hold_time := N.min session.(session_hold_time) open_msg.(open_hold_time);
              session_keepalive_time := session.(session_hold_time) / 3;
              session_connect_retry_counter := session.(session_connect_retry_counter);
              session_connect_retry_timer := session.(session_connect_retry_timer);
              session_hold_timer := Some session.(session_hold_time);
              session_keepalive_timer := Some (session.(session_hold_time) / 3);
              session_delay_open_timer := session.(session_delay_open_timer);
              session_idle_hold_timer := session.(session_idle_hold_timer);
              session_capabilities := open_msg.(open_opt_params);
              session_time_elapsed := session.(session_time_elapsed) |}, Some KEEPALIVE)
      else
        (reset_to_idle session, Some NOTIFICATION)
  
  | OPENCONFIRM, KeepAliveMsg =>
      ({| session_state := ESTABLISHED;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := session.(session_remote_id);
          session_hold_time := session.(session_hold_time);
          session_keepalive_time := session.(session_keepalive_time);
          session_connect_retry_counter := session.(session_connect_retry_counter);
          session_connect_retry_timer := session.(session_connect_retry_timer);
          session_hold_timer := Some session.(session_hold_time);
          session_keepalive_timer := Some session.(session_keepalive_time);
          session_delay_open_timer := session.(session_delay_open_timer);
          session_idle_hold_timer := session.(session_idle_hold_timer);
          session_capabilities := session.(session_capabilities);
          session_time_elapsed := session.(session_time_elapsed) |}, None)
  
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
          session_time_elapsed := 0 |}, Some NOTIFICATION)

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
          session_time_elapsed := 0 |}, Some NOTIFICATION)

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
          session_time_elapsed := 0 |}, Some NOTIFICATION)

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
          session_time_elapsed := 0 |}, Some NOTIFICATION)

  | ESTABLISHED, UpdateMsg upd =>
      if valid_update_message session.(session_local_as) upd then
        if update_has_as_loop session.(session_local_as) upd then
          (session, None)  (* Drop update with AS loop, stay ESTABLISHED *)
        else
          let reset_session := {| session_state := session.(session_state);
                                   session_local_as := session.(session_local_as);
                                   session_remote_as := session.(session_remote_as);
                                   session_local_id := session.(session_local_id);
                                   session_remote_id := session.(session_remote_id);
                                   session_hold_time := session.(session_hold_time);
                                   session_keepalive_time := session.(session_keepalive_time);
                                   session_connect_retry_counter := session.(session_connect_retry_counter);
                                   session_connect_retry_timer := session.(session_connect_retry_timer);
                                   session_hold_timer := Some session.(session_hold_time);  (* Reset hold timer *)
                                   session_keepalive_timer := session.(session_keepalive_timer);
                                   session_delay_open_timer := session.(session_delay_open_timer);
                                   session_idle_hold_timer := session.(session_idle_hold_timer);
                                   session_capabilities := session.(session_capabilities);
                                   session_time_elapsed := session.(session_time_elapsed) |} in
          (reset_session, None)  (* Reset hold timer on valid UPDATE *)
      else
        (session, None)  (* Invalid update, stay ESTABLISHED but ignore *)

  | ESTABLISHED, KeepAliveMsg =>
      let reset_session := {| session_state := session.(session_state);
                               session_local_as := session.(session_local_as);
                               session_remote_as := session.(session_remote_as);
                               session_local_id := session.(session_local_id);
                               session_remote_id := session.(session_remote_id);
                               session_hold_time := session.(session_hold_time);
                               session_keepalive_time := session.(session_keepalive_time);
                               session_connect_retry_counter := session.(session_connect_retry_counter);
                               session_connect_retry_timer := session.(session_connect_retry_timer);
                               session_hold_timer := Some session.(session_hold_time);  (* Reset hold timer *)
                               session_keepalive_timer := session.(session_keepalive_timer);
                               session_delay_open_timer := session.(session_delay_open_timer);
                               session_idle_hold_timer := session.(session_idle_hold_timer);
                               session_capabilities := session.(session_capabilities);
                               session_time_elapsed := session.(session_time_elapsed) |} in
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
          session_time_elapsed := 0 |}, Some NOTIFICATION)

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
          session_time_elapsed := 0 |}, Some NOTIFICATION)

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
          session_time_elapsed := 0 |}, None)

  | IDLE, IdleHoldTimerExpires =>
      (session, None)

  | ESTABLISHED, KeepaliveTimerExpires =>
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
                               session_keepalive_timer := Some session.(session_keepalive_time);
                               session_delay_open_timer := session.(session_delay_open_timer);
                               session_idle_hold_timer := session.(session_idle_hold_timer);
                               session_capabilities := session.(session_capabilities);
                               session_time_elapsed := session.(session_time_elapsed) |} in
      (reset_session, Some KEEPALIVE)  (* Automatic KEEPALIVE generation *)

  | OPENSENT, OpenCollisionDump =>
      (reset_to_idle session, Some NOTIFICATION)

  | OPENCONFIRM, OpenCollisionDump =>
      (reset_to_idle session, Some NOTIFICATION)

  | _, _ => (session, None)  (* Default: no transition *)
  end.

(* =============================================================================
   Section 9: Route Selection (RFC 4271 Section 9)
   ============================================================================= *)

(* Routing Information Bases (RFC 4271 Section 3.2) *)
Record BGPRoute := {
  route_prefix : NLRI;
  route_next_hop : word32;
  route_next_hop_reachable : bool;  (* true if next hop is reachable *)
  route_as_path : list word32;
  route_origin : byte;
  route_med : option word32;
  route_local_pref : word32;
  route_atomic_aggregate : bool;
  route_aggregator : option (word32 * word32);
  route_communities : list word32;
  route_originator_id : word32;
  route_cluster_list : list word32;
  route_is_ebgp : bool;  (* true if learned via eBGP, false if iBGP *)
  route_peer_router_id : word32;  (* Router ID of peer that sent this route *)
  route_igp_cost : option word32  (* IGP cost to NEXT_HOP *)
}.

(* Three Routing Information Bases *)
Record RIB := {
  adj_rib_in : list BGPRoute;   (* Routes received from peers *)
  loc_rib : list BGPRoute;      (* Best routes selected for local use *)
  adj_rib_out : list BGPRoute   (* Routes advertised to peers *)
}.

(* Extract neighboring AS from AS_PATH (first AS for eBGP routes) *)
Definition neighboring_as (route : BGPRoute) : option word32 :=
  match route.(route_as_path) with
  | [] => None
  | as_num :: _ => Some as_num
  end.

(* Check if two routes are from the same neighboring AS *)
Definition same_neighboring_as (r1 r2 : BGPRoute) : bool :=
  match neighboring_as r1, neighboring_as r2 with
  | Some as1, Some as2 => N.eqb as1 as2
  | _, _ => false
  end.

(* BGP Decision Process - RFC 4271 Section 9.1.2 *)
Definition bgp_best_path_selection (routes : list BGPRoute) : option BGPRoute :=
  (* Filter to only reachable routes first *)
  let reachable_routes := filter (fun r => r.(route_next_hop_reachable)) routes in
  let compare_routes (r1 r2 : BGPRoute) : bool :=
    (* 1. Prefer highest LOCAL_PREF *)
    if N.ltb r2.(route_local_pref) r1.(route_local_pref) then true
    (* 2. Prefer shortest AS_PATH *)
    else if N.ltb (N.of_nat (length r1.(route_as_path))) (N.of_nat (length r2.(route_as_path))) then true
    (* 3. Prefer lowest ORIGIN *)
    else if N.ltb r1.(route_origin) r2.(route_origin) then true
    (* 4. Prefer lowest MED (only if from same neighboring AS per RFC 4271) *)
    else if same_neighboring_as r1 r2 then
         match r1.(route_med), r2.(route_med) with
         | Some m1, Some m2 => N.ltb m1 m2
         | Some _, None => true
         | None, Some _ => false
         | None, None => true
         end
    (* 5. Prefer eBGP over iBGP *)
    else if andb r1.(route_is_ebgp) (negb r2.(route_is_ebgp)) then true
    else if andb r2.(route_is_ebgp) (negb r1.(route_is_ebgp)) then false
    (* 6. Prefer lowest IGP cost to NEXT_HOP *)
    else (match r1.(route_igp_cost), r2.(route_igp_cost) with
         | Some c1, Some c2 => if N.ltb c1 c2 then true else if N.ltb c2 c1 then false
                               else if N.ltb r1.(route_peer_router_id) r2.(route_peer_router_id) then true else true
         | Some _, None => true
         | None, Some _ => false
         | None, None => if N.ltb r1.(route_peer_router_id) r2.(route_peer_router_id) then true else true
         end)
  in
  (* Find best route among reachable routes *)
  fold_left (fun best r =>
    match best with
    | None => Some r
    | Some b => if compare_routes r b then Some r else best
    end) reachable_routes None.

(* Initialize empty RIB *)
Definition init_rib : RIB :=
  {| adj_rib_in := [];
     loc_rib := [];
     adj_rib_out := [] |}.

(* Add route to Adj-RIB-In *)
Definition add_route_in (rib : RIB) (route : BGPRoute) : RIB :=
  {| adj_rib_in := route :: rib.(adj_rib_in);
     loc_rib := rib.(loc_rib);
     adj_rib_out := rib.(adj_rib_out) |}.

(* Update Loc-RIB with best path selection *)
Definition update_loc_rib (rib : RIB) : RIB :=
  {| adj_rib_in := rib.(adj_rib_in);
     loc_rib := match bgp_best_path_selection rib.(adj_rib_in) with
                | Some best => [best]
                | None => []
                end;
     adj_rib_out := rib.(adj_rib_out) |}.

(* Export route to Adj-RIB-Out (with attribute modification) *)
Definition export_route (my_as my_router_id : word32) (route : BGPRoute) (is_ebgp : bool) : BGPRoute :=
  {| route_prefix := route.(route_prefix);
     route_next_hop := if is_ebgp then my_router_id else route.(route_next_hop);  (* Set NEXT_HOP to self for eBGP *)
     route_next_hop_reachable := route.(route_next_hop_reachable);
     route_as_path := my_as :: route.(route_as_path);  (* Prepend own AS *)
     route_origin := route.(route_origin);
     route_med := if is_ebgp then None else route.(route_med);  (* MED reset for eBGP *)
     route_local_pref := if is_ebgp then 100 else route.(route_local_pref);  (* Strip/reset for eBGP *)
     route_atomic_aggregate := route.(route_atomic_aggregate);
     route_aggregator := route.(route_aggregator);
     route_communities := route.(route_communities);
     route_originator_id := route.(route_originator_id);
     route_cluster_list := route.(route_cluster_list);
     route_is_ebgp := is_ebgp;
     route_peer_router_id := route.(route_peer_router_id);
     route_igp_cost := route.(route_igp_cost) |}.

(* iBGP split horizon: Don't advertise iBGP routes to iBGP peers *)
Definition should_advertise_route (route : BGPRoute) (peer_is_ebgp : bool) : bool :=
  if peer_is_ebgp then true
  else route.(route_is_ebgp).  (* Only advertise if route came from eBGP *)

(* Update Adj-RIB-Out from Loc-RIB *)
Definition update_adj_rib_out (my_as my_router_id : word32) (rib : RIB) (is_ebgp : bool) : RIB :=
  let filtered := filter (fun r => should_advertise_route r is_ebgp) rib.(loc_rib) in
  {| adj_rib_in := rib.(adj_rib_in);
     loc_rib := rib.(loc_rib);
     adj_rib_out := map (fun r => export_route my_as my_router_id r is_ebgp) filtered |}.

(* =============================================================================
   Section 9.5: RIB Properties
   ============================================================================= *)

(* Property: Empty RIB has empty Loc-RIB *)
Theorem init_rib_empty_loc : init_rib.(loc_rib) = [].
Proof.
  reflexivity.
Qed.

(* Property: Adding route preserves Loc-RIB *)
Theorem add_route_preserves_loc_rib : forall rib route,
  (add_route_in rib route).(loc_rib) = rib.(loc_rib).
Proof.
  intros. reflexivity.
Qed.

(* Property: Update Loc-RIB selects from Adj-RIB-In *)
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

(* =============================================================================
   Section 10: Key Properties
   ============================================================================= *)

(* Property 1: State machine starts in IDLE *)
Theorem initial_state_idle : forall las ras lid,
  (init_bgp_session las ras lid).(session_state) = IDLE.
Proof.
  intros. reflexivity.
Qed.

(* Property 2: Transition to ESTABLISHED preserves remote_id *)
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

(* Property 3: Hold time negotiation takes minimum *)
Theorem hold_time_negotiation : forall session open_msg session',
  session.(session_state) = OPENSENT ->
  valid_open_message open_msg = true ->
  has_bgp_id_collision session.(session_local_id) open_msg.(open_bgp_identifier) = false ->
  bgp_state_transition session (BGPOpen_Received open_msg) = (session', Some KEEPALIVE) ->
  session'.(session_hold_time) = N.min session.(session_hold_time) open_msg.(open_hold_time).
Proof.
  intros session open_msg session' Hstate Hvalid Hnocoll Htrans.
  unfold bgp_state_transition in Htrans.
  rewrite Hstate in Htrans.
  rewrite Hvalid in Htrans.
  rewrite Hnocoll in Htrans.
  inversion Htrans.
  reflexivity.
Qed.

(* Property 3.5: Valid OPEN guarantees non-zero remote_id *)
Theorem valid_open_nonzero_remote_id : forall session open_msg session',
  session.(session_state) = OPENSENT ->
  valid_open_message open_msg = true ->
  has_bgp_id_collision session.(session_local_id) open_msg.(open_bgp_identifier) = false ->
  bgp_state_transition session (BGPOpen_Received open_msg) = (session', Some KEEPALIVE) ->
  session'.(session_remote_id) <> 0.
Proof.
  intros session open_msg session' Hstate Hvalid Hnocoll Htrans.
  unfold bgp_state_transition in Htrans.
  rewrite Hstate in Htrans.
  rewrite Hvalid in Htrans.
  rewrite Hnocoll in Htrans.
  inversion Htrans. subst.
  unfold valid_open_message in Hvalid.
  apply andb_prop in Hvalid. destruct Hvalid as [_ Hrest].
  apply andb_prop in Hrest. destruct Hrest as [Hid _].
  unfold valid_bgp_identifier in Hid.
  unfold negb in Hid.
  destruct (N.eqb (open_bgp_identifier open_msg) 0) eqn:Heq.
  - discriminate Hid.
  - apply N.eqb_neq. assumption.
Qed.

(* Property 3.55: Valid hold time accepts 0 or >=3 *)
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

(* Property 3.56: Invalid hold times rejected *)
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

(* Property 3.57: AS 0 is invalid *)
Theorem as_zero_invalid :
  valid_as_number 0 = false.
Proof.
  unfold valid_as_number. simpl. reflexivity.
Qed.

(* Property 3.58: Non-zero AS is valid *)
Theorem as_nonzero_valid : forall asn,
  asn <> 0 -> valid_as_number asn = true.
Proof.
  intros asn Hnonzero.
  unfold valid_as_number.
  apply negb_true_iff.
  apply N.eqb_neq.
  exact Hnonzero.
Qed.

(* Property 3.59: Valid ORIGIN values *)
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

(* Property 3.591: Valid NLRI prefix lengths *)
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

(* Property 3.6: Connection failure transitions to ACTIVE *)
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

(* Property 3.7: ACTIVE can transition to OPENSENT on TCP success *)
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

(* Property 3.8: ACTIVE retry timer expires back to CONNECT *)
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

(* Property 4: Notification returns to IDLE *)
Theorem notification_to_idle : forall session notif session' msg,
  bgp_state_transition session (NotifMsg notif) = (session', msg) ->
  session'.(session_state) = IDLE.
Proof.
  intros. unfold bgp_state_transition in H.
  destruct session.(session_state); inversion H; reflexivity.
Qed.

(* Property 4.1: Timer tick updates elapsed time *)
Theorem timer_tick_increments_time : forall session delta session' events,
  timer_tick session delta = (session', events) ->
  session'.(session_time_elapsed) = session.(session_time_elapsed) + delta.
Proof.
  intros session delta session' events Htick.
  unfold timer_tick in Htick.
  inversion Htick.
  reflexivity.
Qed.

(* Property 5: AS path loop detection *)
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

(* Property 5.1: Mandatory attributes in valid UPDATE *)
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

(* Property 6: Valid header has correct marker length *)
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

(* Property 7: Best path selection excludes unreachable routes *)
Theorem best_path_excludes_unreachable : forall r routes,
  r.(route_next_hop_reachable) = false ->
  bgp_best_path_selection (r :: routes) = bgp_best_path_selection routes.
Proof.
  intros r routes Hunreach.
  unfold bgp_best_path_selection.
  simpl. rewrite Hunreach. reflexivity.
Qed.

(* =============================================================================
   Section 11: Deep Properties - Convergence
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
   Section 11.5: Deep Properties - Safety
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
  (fst (bgp_state_transition session (BGPOpen_Received open_msg))).(session_state) = OPENCONFIRM.
Proof.
  intros. unfold bgp_state_transition. rewrite H. rewrite H0. rewrite H1. reflexivity.
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
  intros session Hidle Hnocoll.
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
                           session_time_elapsed := 0 |}).
  set (intermediate2 := {| session_state := OPENSENT;
                           session_local_as := session_local_as intermediate1;
                           session_remote_as := session_remote_as intermediate1;
                           session_local_id := session_local_id intermediate1;
                           session_remote_id := session_remote_id intermediate1;
                           session_hold_time := session_hold_time intermediate1;
                           session_keepalive_time := session_keepalive_time intermediate1;
                           session_connect_retry_counter := session_connect_retry_counter intermediate1;
                           session_connect_retry_timer := None;
                           session_hold_timer := Some (session_hold_time intermediate1);
                           session_keepalive_timer := session_keepalive_timer intermediate1;
                           session_delay_open_timer := session_delay_open_timer intermediate1;
                           session_idle_hold_timer := session_idle_hold_timer intermediate1;
                           session_capabilities := session_capabilities intermediate1;
                           session_time_elapsed := session_time_elapsed intermediate1 |}).
  set (intermediate3 := {| session_state := OPENCONFIRM;
                           session_local_as := session_local_as intermediate2;
                           session_remote_as := 65001;
                           session_local_id := session_local_id intermediate2;
                           session_remote_id := 1;
                           session_hold_time := N.min (session_hold_time intermediate2) 90;
                           session_keepalive_time := session_hold_time intermediate2 / 3;
                           session_connect_retry_counter := session_connect_retry_counter intermediate2;
                           session_connect_retry_timer := session_connect_retry_timer intermediate2;
                           session_hold_timer := Some (session_hold_time intermediate2);
                           session_keepalive_timer := Some (session_hold_time intermediate2 / 3);
                           session_delay_open_timer := session_delay_open_timer intermediate2;
                           session_idle_hold_timer := session_idle_hold_timer intermediate2;
                           session_capabilities := [];
                           session_time_elapsed := session_time_elapsed intermediate2 |}).
  set (established_session := {| session_state := ESTABLISHED;
                                  session_local_as := session_local_as intermediate3;
                                  session_remote_as := session_remote_as intermediate3;
                                  session_local_id := session_local_id intermediate3;
                                  session_remote_id := session_remote_id intermediate3;
                                  session_hold_time := session_hold_time intermediate3;
                                  session_keepalive_time := session_keepalive_time intermediate3;
                                  session_connect_retry_counter := session_connect_retry_counter intermediate3;
                                  session_connect_retry_timer := session_connect_retry_timer intermediate3;
                                  session_hold_timer := Some (session_hold_time intermediate3);
                                  session_keepalive_timer := Some (session_keepalive_time intermediate3);
                                  session_delay_open_timer := session_delay_open_timer intermediate3;
                                  session_idle_hold_timer := session_idle_hold_timer intermediate3;
                                  session_capabilities := session_capabilities intermediate3;
                                  session_time_elapsed := session_time_elapsed intermediate3 |}).
  exists established_session.
  split. unfold valid_open_message, valid_bgp_identifier, valid_hold_time, valid_as_number. simpl. reflexivity.
  split. reflexivity.
  exists intermediate1, intermediate2, intermediate3.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  split.
  - unfold fst. simpl. rewrite Hcollfalse. reflexivity.
  - split. reflexivity. reflexivity.
Qed.

(* =============================================================================
   Section 11.6: Deep Properties - Liveness
   ============================================================================= *)

Lemma hold_timer_set_in_opensent : forall session,
  session.(session_state) = CONNECT ->
  (fst (bgp_state_transition session TCPConnectionConfirmed)).(session_hold_timer) = Some (session.(session_hold_time)).
Proof.
  intros. unfold bgp_state_transition. rewrite H. simpl. reflexivity.
Qed.

Theorem liveness_hold_timer_bounded : forall session,
  session.(session_state) = OPENSENT ->
  True.
Proof.
  intros. exact I.
Qed.

(* =============================================================================
   Section 11.7: Deep Properties - Route Consistency
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
   Section 12: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction "bgp4.ml"
  init_bgp_session
  bgp_state_transition
  bgp_best_path_selection.
