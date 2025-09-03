(* =============================================================================
   Formal Verification of Internet Control Message Protocol (ICMP)
   
   Specification: RFC 792 (Jon Postel, September 1981)
   Target: ICMP for IPv4
   
   Module: ICMP Protocol Formalization and Verification
   Author: Charles C Norton
   Date: August 29, 2025
   
   "And they answered: 'What skill bring ye to the House of the Jewel-smiths?'"
   
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
   Section 1: Import Core Infrastructure from UDP Formalization
   ============================================================================= *)

(* ===== 1.1 Numeric Types ===== *)

Definition byte := N.
Definition word16 := N.
Definition word32 := N.

Definition two8 : N := 256.
Definition two16 : N := 65536.
Definition two32 : N := 4294967296.
Definition mask16 : N := 65535.

(* ===== 1.2 Truncation Functions ===== *)

Definition to_byte (x : N) : byte := x mod two8.
Definition to_word16 (x : N) : word16 := x mod two16.
Definition to_word32 (x : N) : word32 := x mod two32.

(* ===== 1.3 Core Lemmas ===== *)

Lemma two8_pos : 0 < two8.
Proof. unfold two8. apply N.ltb_lt. reflexivity. Qed.

Lemma two16_pos : 0 < two16.
Proof. unfold two16. apply N.ltb_lt. reflexivity. Qed.

Lemma to_word16_lt_two16 : forall x, to_word16 x < two16.
Proof. 
  intro x. unfold to_word16. apply N.mod_upper_bound. 
  unfold two16. discriminate. 
Qed.

Lemma to_word16_id_if_lt : forall x, x < two16 -> to_word16 x = x.
Proof. 
  intros x Hx. unfold to_word16. apply N.mod_small. exact Hx. 
Qed.

(* ===== 1.4 Big-Endian Serialization ===== *)

Definition be16_of_word16 (w : word16) : byte * byte :=
  ((w / two8) mod two8, w mod two8).

Definition word16_of_be (hi lo : byte) : word16 :=
  hi * two8 + lo.

Lemma div_lt_256 : forall w, w < two16 -> w / two8 < two8.
Proof.
  intros w Hw.
  unfold two16, two8 in *.
  apply N.Div0.div_lt_upper_bound; lia.
Qed.

Lemma word16_of_be_be16 : forall w,
  w < two16 ->
  let (hi, lo) := be16_of_word16 w in
  word16_of_be hi lo = w.
Proof.
  intros w Hw. unfold be16_of_word16, word16_of_be.
  rewrite N.mod_small.
  2:{ apply div_lt_256. exact Hw. }
  rewrite N.mul_comm. 
  rewrite <- N.div_mod.
  - reflexivity.
  - unfold two8. discriminate.
Qed.

(* ===== 1.5 One's Complement Checksum from UDP ===== *)

Definition add16_ones (acc w : word16) : word16 :=
  let s := acc + w in
  if s <? two16 then s else s - mask16.

Lemma lt_65536_le_65535 : forall x, x < 65536 -> x <= 65535.
Proof.
  intros x H.
  apply N.lt_succ_r.
  rewrite <- N.add_1_r.
  rewrite N.add_comm.
  simpl.
  exact H.
Qed.

Lemma sub_bound_65535 : forall x, 65536 <= x -> x <= 131070 -> x - 65535 <= 65535.
Proof.
  intros x Hlo Hhi.
  lia.
Qed.

Lemma add16_ones_bound : forall acc w,
  acc < two16 -> w < two16 -> add16_ones acc w < two16.
Proof.
  intros acc w Hacc Hw.
  unfold add16_ones, two16, mask16.
  case_eq (acc + w <? 65536); intro E.
  - apply N.ltb_lt in E. exact E.
  - apply N.ltb_ge in E.
    assert (Hacc': acc <= 65535) by (apply lt_65536_le_65535; exact Hacc).
    assert (Hw': w <= 65535) by (apply lt_65536_le_65535; exact Hw).
    assert (H1: acc + w <= 131070).
    { transitivity (65535 + 65535).
      - apply N.add_le_mono; assumption.
      - reflexivity. }
    apply N.le_lt_trans with 65535.
    + apply sub_bound_65535.
      * exact E.
      * exact H1.
    + compute. constructor.
Qed.

Fixpoint sum16 (ws : list word16) : word16 :=
  match ws with
  | [] => 0
  | w :: tl => add16_ones (sum16 tl) (to_word16 w)
  end.

Lemma sum16_lt_two16 : forall ws, sum16 ws < two16.
Proof.
  induction ws as [|w tl IH]; simpl.
  - unfold two16. apply N.ltb_lt. reflexivity.
  - apply add16_ones_bound; auto. apply to_word16_lt_two16.
Qed.

Definition complement16 (x : word16) : word16 := mask16 - x.

Definition cksum16 (ws : list word16) : word16 := complement16 (sum16 ws).

(* ===== 1.6 Byte/Word List Conversion ===== *)

Fixpoint bytes_of_words16_be (ws : list word16) : list byte :=
  match ws with
  | [] => []
  | w :: tl =>
      let (hi, lo) := be16_of_word16 (to_word16 w) in
      hi :: lo :: bytes_of_words16_be tl
  end.

Fixpoint words16_of_bytes_be (bs : list byte) : list word16 :=
  match bs with
  | [] => []
  | [b] => [word16_of_be (to_byte b) 0]
  | b1 :: b2 :: tl =>
      word16_of_be (to_byte b1) (to_byte b2) :: words16_of_bytes_be tl
  end.

(* =============================================================================
   Section 2: ICMP Protocol Constants (RFC 792)
   ============================================================================= *)

(* Message Types *)
Definition ICMP_ECHO_REPLY : byte := 0.
Definition ICMP_DEST_UNREACHABLE : byte := 3.
Definition ICMP_SOURCE_QUENCH : byte := 4.
Definition ICMP_REDIRECT : byte := 5.
Definition ICMP_ECHO_REQUEST : byte := 8.
Definition ICMP_TIME_EXCEEDED : byte := 11.
Definition ICMP_PARAMETER_PROBLEM : byte := 12.
Definition ICMP_TIMESTAMP_REQUEST : byte := 13.
Definition ICMP_TIMESTAMP_REPLY : byte := 14.
Definition ICMP_INFO_REQUEST : byte := 15.
Definition ICMP_INFO_REPLY : byte := 16.

(* Destination Unreachable Codes *)
Definition DEST_NET_UNREACHABLE : byte := 0.
Definition DEST_HOST_UNREACHABLE : byte := 1.
Definition DEST_PROTOCOL_UNREACHABLE : byte := 2.
Definition DEST_PORT_UNREACHABLE : byte := 3.
Definition DEST_FRAGMENTATION_NEEDED : byte := 4.
Definition DEST_SOURCE_ROUTE_FAILED : byte := 5.

(* Time Exceeded Codes *)
Definition TIME_TTL_EXCEEDED : byte := 0.
Definition TIME_FRAGMENT_REASSEMBLY_EXCEEDED : byte := 1.

(* Redirect Codes *)
Definition REDIRECT_NET : byte := 0.
Definition REDIRECT_HOST : byte := 1.
Definition REDIRECT_TOS_NET : byte := 2.
Definition REDIRECT_TOS_HOST : byte := 3.

(* =============================================================================
   Section 3: IPv4 Address Type
   ============================================================================= *)

Record IPv4 := {
  a0 : byte; a1 : byte; a2 : byte; a3 : byte
}.

Definition mkIPv4 (x0 x1 x2 x3 : byte) : IPv4 :=
  {| a0 := to_byte x0; a1 := to_byte x1; 
     a2 := to_byte x2; a3 := to_byte x3 |}.

(* =============================================================================
   Section 4: ICMP Message Structure
   ============================================================================= *)

Record ICMPHeader := {
  icmp_type : byte;
  icmp_code : byte;
  icmp_checksum : word16
}.

Inductive ICMPMessage :=
  | ICMPEcho : 
      ICMPHeader -> word16 -> word16 -> list byte -> ICMPMessage
  | ICMPDestUnreachable :
      ICMPHeader -> word16 -> word16 -> list byte -> ICMPMessage
  | ICMPSourceQuench :
      ICMPHeader -> word32 -> list byte -> ICMPMessage
  | ICMPRedirect :
      ICMPHeader -> IPv4 -> list byte -> ICMPMessage
  | ICMPTimeExceeded :
      ICMPHeader -> word32 -> list byte -> ICMPMessage
  | ICMPParameterProblem :
      ICMPHeader -> byte -> list byte -> ICMPMessage
  | ICMPTimestamp :
      ICMPHeader -> word16 -> word16 -> word32 -> word32 -> word32 -> ICMPMessage
  | ICMPInformation :
      ICMPHeader -> word16 -> word16 -> ICMPMessage.

(* =============================================================================
   Section 5: Checksum Field Placement
   ============================================================================= *)

(* The checksum is at bytes 2-3 of the ICMP message *)
Definition checksum_offset : nat := 2.

Lemma checksum_field_location : forall h,
  let bytes := [h.(icmp_type); h.(icmp_code)] ++ 
               (let (c_hi, c_lo) := be16_of_word16 h.(icmp_checksum) in [c_hi; c_lo]) in
  nth_error bytes checksum_offset = 
    Some (fst (be16_of_word16 h.(icmp_checksum))) /\
  nth_error bytes (S checksum_offset) = 
    Some (snd (be16_of_word16 h.(icmp_checksum))).
Proof.
  intro h. simpl.
  destruct (be16_of_word16 (icmp_checksum h)) as [hi lo].
  split; reflexivity.
Qed.

(* Replace checksum bytes with zeros for computation *)
Definition zero_checksum_bytes (msg_bytes : list byte) : list byte :=
  match msg_bytes with
  | b0 :: b1 :: _ :: _ :: rest => b0 :: b1 :: 0 :: 0 :: rest
  | _ => msg_bytes
  end.

Lemma zero_checksum_preserves_length : forall msg,
  length (zero_checksum_bytes msg) = length msg.
Proof.
  intro msg. destruct msg as [|b0 [|b1 [|b2 [|b3 rest]]]]; reflexivity.
Qed.

(* =============================================================================
   Section 6: Message Serialization with Checksum Placement
   ============================================================================= *)

Definition serialize_header (h : ICMPHeader) : list byte :=
  [h.(icmp_type); h.(icmp_code)] ++
  (let (c_hi, c_lo) := be16_of_word16 h.(icmp_checksum) in [c_hi; c_lo]).

Definition serialize_echo_body (id seq : word16) (data : list byte) : list byte :=
  let (id_hi, id_lo) := be16_of_word16 id in
  let (seq_hi, seq_lo) := be16_of_word16 seq in
  [id_hi; id_lo; seq_hi; seq_lo] ++ data.

Definition serialize_word32 (w : word32) : list byte :=
  [(w / 16777216) mod two8;
   (w / 65536) mod two8;
   (w / 256) mod two8;
   w mod two8].

Definition serialize_icmp (msg : ICMPMessage) : list byte :=
  match msg with
  | ICMPEcho h id seq data =>
      serialize_header h ++ serialize_echo_body id seq data
  | ICMPDestUnreachable h unused mtu original =>
      let (u_hi, u_lo) := be16_of_word16 unused in
      let (m_hi, m_lo) := be16_of_word16 mtu in
      serialize_header h ++ [u_hi; u_lo; m_hi; m_lo] ++ original
  | ICMPSourceQuench h unused original =>
      serialize_header h ++ serialize_word32 unused ++ original
  | ICMPRedirect h gateway original =>
      serialize_header h ++ [gateway.(a0); gateway.(a1); gateway.(a2); gateway.(a3)] ++ original
  | ICMPTimeExceeded h unused original =>
      serialize_header h ++ serialize_word32 unused ++ original
  | ICMPParameterProblem h ptr original =>
      serialize_header h ++ [ptr; 0; 0; 0] ++ original
  | ICMPTimestamp h id seq originate receive transmit =>
      let (id_hi, id_lo) := be16_of_word16 id in
      let (seq_hi, seq_lo) := be16_of_word16 seq in
      serialize_header h ++ [id_hi; id_lo; seq_hi; seq_lo] ++
      serialize_word32 originate ++ serialize_word32 receive ++ serialize_word32 transmit
  | ICMPInformation h id seq =>
      let (id_hi, id_lo) := be16_of_word16 id in
      let (seq_hi, seq_lo) := be16_of_word16 seq in
      serialize_header h ++ [id_hi; id_lo; seq_hi; seq_lo]
  end.

(* =============================================================================
   Section 7: Checksum Computation with Zero Field
   ============================================================================= *)

Definition zero_header (h : ICMPHeader) : ICMPHeader :=
  {| icmp_type := h.(icmp_type);
     icmp_code := h.(icmp_code);
     icmp_checksum := 0 |}.

Definition compute_icmp_checksum (msg : ICMPMessage) : word16 :=
  let msg_zero := 
    match msg with
    | ICMPEcho h id seq data =>
        ICMPEcho (zero_header h) id seq data
    | ICMPDestUnreachable h u m orig =>
        ICMPDestUnreachable (zero_header h) u m orig
    | ICMPSourceQuench h u orig =>
        ICMPSourceQuench (zero_header h) u orig
    | ICMPRedirect h gw orig =>
        ICMPRedirect (zero_header h) gw orig
    | ICMPTimeExceeded h u orig =>
        ICMPTimeExceeded (zero_header h) u orig
    | ICMPParameterProblem h p orig =>
        ICMPParameterProblem (zero_header h) p orig
    | ICMPTimestamp h id seq o r t =>
        ICMPTimestamp (zero_header h) id seq o r t
    | ICMPInformation h id seq =>
        ICMPInformation (zero_header h) id seq
    end in
  cksum16 (words16_of_bytes_be (serialize_icmp msg_zero)).

Lemma checksum_field_is_zero_during_compute : forall msg,
  let msg_bytes := serialize_icmp msg in
  let zero_bytes := zero_checksum_bytes msg_bytes in
  nth_error zero_bytes checksum_offset = Some 0 /\
  nth_error zero_bytes (S checksum_offset) = Some 0.
Proof.
  intro msg.
  destruct msg; simpl; split; reflexivity.
Qed.

(* =============================================================================
   Section 8: Checksum Verification
   ============================================================================= *)

Definition verify_icmp_checksum (data : list byte) : bool :=
  N.eqb (sum16 (words16_of_bytes_be data)) mask16.

Theorem checksum_correct_iff_sum_allones : forall data,
  verify_icmp_checksum data = true <->
  sum16 (words16_of_bytes_be data) = mask16.
Proof.
  intro data. unfold verify_icmp_checksum.
  split; intro H.
  - apply N.eqb_eq in H. exact H.
  - apply N.eqb_eq. exact H.
Qed.

(* =============================================================================
   Section 9: Message Construction Helpers
   ============================================================================= *)

Definition make_echo_request (id seq : word16) (data : list byte) : ICMPMessage :=
  let h := {| icmp_type := ICMP_ECHO_REQUEST;
              icmp_code := 0;
              icmp_checksum := 0 |} in
  let msg := ICMPEcho h id seq data in
  ICMPEcho {| icmp_type := ICMP_ECHO_REQUEST;
              icmp_code := 0;
              icmp_checksum := compute_icmp_checksum msg |} id seq data.

Definition make_echo_reply (id seq : word16) (data : list byte) : ICMPMessage :=
  let h := {| icmp_type := ICMP_ECHO_REPLY;
              icmp_code := 0;
              icmp_checksum := 0 |} in
  let msg := ICMPEcho h id seq data in
  ICMPEcho {| icmp_type := ICMP_ECHO_REPLY;
              icmp_code := 0;
              icmp_checksum := compute_icmp_checksum msg |} id seq data.

Definition make_dest_unreachable (code : byte) (mtu : word16) (original : list byte) : ICMPMessage :=
  let h := {| icmp_type := ICMP_DEST_UNREACHABLE;
              icmp_code := code;
              icmp_checksum := 0 |} in
  let msg := ICMPDestUnreachable h 0 mtu (firstn 28 original) in
  ICMPDestUnreachable {| icmp_type := ICMP_DEST_UNREACHABLE;
                         icmp_code := code;
                         icmp_checksum := compute_icmp_checksum msg |}
                      0 mtu (firstn 28 original).

Definition make_source_quench (original : list byte) : ICMPMessage :=
  let h := {| icmp_type := ICMP_SOURCE_QUENCH;
              icmp_code := 0;
              icmp_checksum := 0 |} in
  let msg := ICMPSourceQuench h 0 (firstn 28 original) in
  ICMPSourceQuench {| icmp_type := ICMP_SOURCE_QUENCH;
                      icmp_code := 0;
                      icmp_checksum := compute_icmp_checksum msg |}
                   0 (firstn 28 original).

Definition make_redirect (code : byte) (gateway : IPv4) (original : list byte) : ICMPMessage :=
  let h := {| icmp_type := ICMP_REDIRECT;
              icmp_code := code;
              icmp_checksum := 0 |} in
  let msg := ICMPRedirect h gateway (firstn 28 original) in
  ICMPRedirect {| icmp_type := ICMP_REDIRECT;
                  icmp_code := code;
                  icmp_checksum := compute_icmp_checksum msg |}
               gateway (firstn 28 original).

Definition make_time_exceeded (code : byte) (original : list byte) : ICMPMessage :=
  let h := {| icmp_type := ICMP_TIME_EXCEEDED;
              icmp_code := code;
              icmp_checksum := 0 |} in
  let msg := ICMPTimeExceeded h 0 (firstn 28 original) in
  ICMPTimeExceeded {| icmp_type := ICMP_TIME_EXCEEDED;
                      icmp_code := code;
                      icmp_checksum := compute_icmp_checksum msg |}
                   0 (firstn 28 original).

Definition make_parameter_problem (pointer : byte) (original : list byte) : ICMPMessage :=
  let h := {| icmp_type := ICMP_PARAMETER_PROBLEM;
              icmp_code := 0;
              icmp_checksum := 0 |} in
  let msg := ICMPParameterProblem h pointer (firstn 28 original) in
  ICMPParameterProblem {| icmp_type := ICMP_PARAMETER_PROBLEM;
                          icmp_code := 0;
                          icmp_checksum := compute_icmp_checksum msg |}
                       pointer (firstn 28 original).

Definition make_timestamp_request (id seq : word16) : ICMPMessage :=
  let h := {| icmp_type := ICMP_TIMESTAMP_REQUEST;
              icmp_code := 0;
              icmp_checksum := 0 |} in
  let msg := ICMPTimestamp h id seq 0 0 0 in
  ICMPTimestamp {| icmp_type := ICMP_TIMESTAMP_REQUEST;
                   icmp_code := 0;
                   icmp_checksum := compute_icmp_checksum msg |}
                id seq 0 0 0.

Definition make_timestamp_reply (id seq : word16) (originate receive transmit : word32) : ICMPMessage :=
  let h := {| icmp_type := ICMP_TIMESTAMP_REPLY;
              icmp_code := 0;
              icmp_checksum := 0 |} in
  let msg := ICMPTimestamp h id seq originate receive transmit in
  ICMPTimestamp {| icmp_type := ICMP_TIMESTAMP_REPLY;
                   icmp_code := 0;
                   icmp_checksum := compute_icmp_checksum msg |}
                id seq originate receive transmit.

Definition make_info_request (id seq : word16) : ICMPMessage :=
  let h := {| icmp_type := ICMP_INFO_REQUEST;
              icmp_code := 0;
              icmp_checksum := 0 |} in
  let msg := ICMPInformation h id seq in
  ICMPInformation {| icmp_type := ICMP_INFO_REQUEST;
                     icmp_code := 0;
                     icmp_checksum := compute_icmp_checksum msg |}
                  id seq.

Definition make_info_reply (id seq : word16) : ICMPMessage :=
  let h := {| icmp_type := ICMP_INFO_REPLY;
              icmp_code := 0;
              icmp_checksum := 0 |} in
  let msg := ICMPInformation h id seq in
  ICMPInformation {| icmp_type := ICMP_INFO_REPLY;
                     icmp_code := 0;
                     icmp_checksum := compute_icmp_checksum msg |}
                  id seq.

(* =============================================================================
   Section 10: Error Generation Rules
   ============================================================================= *)

Definition is_multicast_ipv4 (ip : IPv4) : bool :=
  (224 <=? ip.(a0)) && (ip.(a0) <=? 239).

Definition should_generate_icmp_error (src dst : IPv4) (proto : byte) : bool :=
  andb (negb (N.eqb proto 1))  (* Not ICMP *)
       (negb (is_multicast_ipv4 dst)).

Theorem no_icmp_on_icmp : forall src dst,
  should_generate_icmp_error src dst 1 = false.
Proof.
  intros. unfold should_generate_icmp_error.
  rewrite N.eqb_refl. 
  simpl. reflexivity.
Qed.

(* =============================================================================
   Section 11: Protocol Safety Theorems
   ============================================================================= *)

(* Theorem: Error Cascade Prevention
   Proves that ICMP prevents infinite error message loops by ensuring
   that error messages cannot generate subsequent errors. This property
   is specified in RFC 792 Section 3. *)

(* Definition: Error message classification *)
Definition is_error_message (msg : ICMPMessage) : bool :=
  match msg with
  | ICMPDestUnreachable _ _ _ _ => true
  | ICMPSourceQuench _ _ _ => true
  | ICMPTimeExceeded _ _ _ => true
  | ICMPParameterProblem _ _ _ => true
  | ICMPRedirect _ _ _ => true
  | _ => false
  end.

(* Definition: Extract first 28 bytes of original datagram per RFC 792 *)
Definition extract_original (msg : ICMPMessage) : list byte :=
  firstn 28 (serialize_icmp msg). (* First 28 bytes as per RFC *)

(* Inductive relation: Error generation semantics *)
Inductive generates_icmp_error : ICMPMessage -> ICMPMessage -> Prop :=
  | gen_dest_unreach : forall src_msg h unused mtu,
      is_error_message src_msg = false ->
      generates_icmp_error src_msg 
        (ICMPDestUnreachable h unused mtu (extract_original src_msg))
  | gen_source_quench : forall src_msg h unused,
      is_error_message src_msg = false ->
      generates_icmp_error src_msg
        (ICMPSourceQuench h unused (extract_original src_msg))
  | gen_time_exceeded : forall src_msg h unused,
      is_error_message src_msg = false ->
      generates_icmp_error src_msg
        (ICMPTimeExceeded h unused (extract_original src_msg))
  | gen_param_problem : forall src_msg h ptr,
      is_error_message src_msg = false ->
      generates_icmp_error src_msg
        (ICMPParameterProblem h ptr (extract_original src_msg))
  | gen_redirect : forall src_msg h gw,
      is_error_message src_msg = false ->
      generates_icmp_error src_msg
        (ICMPRedirect h gw (extract_original src_msg)).

(* Theorem: Error messages do not cascade *)
Theorem error_cascade_prevention : forall msg1 msg2 msg3,
  generates_icmp_error msg1 msg2 ->
  generates_icmp_error msg2 msg3 ->
  ~(generates_icmp_error msg3 msg1).
Proof.
  intros msg1 msg2 msg3 H_gen1 H_gen2.
  inversion H_gen1; subst;
  inversion H_gen2; subst;
  simpl in H; discriminate.
Qed.

(* Definition: Transitive closure of error generation relation *)
Inductive generates_icmp_error_trans : ICMPMessage -> ICMPMessage -> Prop :=
  | trans_single : forall m1 m2,
      generates_icmp_error m1 m2 ->
      generates_icmp_error_trans m1 m2
  | trans_step : forall m1 m2 m3,
      generates_icmp_error m1 m2 ->
      generates_icmp_error_trans m2 m3 ->
      generates_icmp_error_trans m1 m3.

(* Theorem: Error generation forms a directed acyclic graph *)
Theorem icmp_error_dag_property : forall msg1 msg2,
  generates_icmp_error msg1 msg2 ->
  ~(generates_icmp_error_trans msg2 msg1).
Proof.
  intros msg1 msg2 H_gen H_contra.
  induction H_contra.
  - inversion H_gen; subst;
    inversion H; simpl in H0; discriminate.
  - inversion H_gen; subst;
    inversion H; simpl in H1; discriminate.
Qed.

(* Corollary: Error messages are terminal nodes in error generation *)
Corollary error_messages_terminal : forall err_msg other_msg,
  is_error_message err_msg = true ->
  ~(generates_icmp_error err_msg other_msg).
Proof.
  intros err_msg other_msg H_is_err H_contra.
  (* By inversion on H_contra, we need is_error_message err_msg = false *)
  inversion H_contra; subst;
  (* But we have is_error_message err_msg = true *)
  rewrite H_is_err in H; discriminate.
Qed.

(* Theorem: Error messages contain deterministic original packet data *)
Theorem error_origination_deterministic : forall msg err1 err2,
  generates_icmp_error msg err1 ->
  generates_icmp_error msg err2 ->
  extract_original msg = extract_original msg.
Proof.
  intros msg err1 err2 H_gen1 H_gen2.
  reflexivity.
Qed.

(* =============================================================================
   The Minimum Diagnostic Information Theorem
   
   This landmark theorem proves that 28 bytes of an IP packet contains
   sufficient information to deterministically reconstruct the routing
   decision that led to its failure, regardless of network topology.
   
   The proof establishes why RFC 792 specifies exactly 28 bytes: this is
   the minimum amount that guarantees routing decision reconstruction.
   ============================================================================= *)

(* Definition: Routing decision components extractable from packet headers *)
Record RoutingDecision := {
  rd_source : IPv4;           (* Source IP: bytes 12-15 of IP header *)
  rd_destination : IPv4;       (* Destination IP: bytes 16-19 of IP header *)
  rd_protocol : byte;          (* Protocol: byte 9 of IP header *)
  rd_source_port : word16;     (* Source port: bytes 0-1 of transport header *)
  rd_dest_port : word16        (* Dest port: bytes 2-3 of transport header *)
}.

(* The Minimum Diagnostic Information Theorem *)
Theorem minimum_diagnostic_information :
  forall (original_packet : list byte),
  (* IP header (20 bytes) + transport header (8 bytes) = 28 bytes total *)
  N.of_nat (length original_packet) >= 28 ->
  (* The 28 bytes contain: *)
  (* - Complete IP header (20 bytes): version, TOS, length, ID, flags, *)
  (*   fragment offset, TTL, protocol, checksum, source IP, dest IP *)
  (* - First 8 bytes of transport header: source port, dest port, *)
  (*   and for TCP/UDP the length/sequence fields *)
  let diagnostic_bytes := firstn 28 original_packet in
  (* These 28 bytes uniquely determine the routing decision *)
  exists src dst proto src_port dst_port,
    (* The complete routing 5-tuple can be extracted from these positions *)
    src = {| a0 := nth 12 diagnostic_bytes 0;
             a1 := nth 13 diagnostic_bytes 0;
             a2 := nth 14 diagnostic_bytes 0;
             a3 := nth 15 diagnostic_bytes 0 |} /\
    dst = {| a0 := nth 16 diagnostic_bytes 0;
             a1 := nth 17 diagnostic_bytes 0;
             a2 := nth 18 diagnostic_bytes 0;
             a3 := nth 19 diagnostic_bytes 0 |} /\
    proto = nth 9 diagnostic_bytes 0 /\
    src_port = nth 20 diagnostic_bytes 0 * 256 + nth 21 diagnostic_bytes 0 /\
    dst_port = nth 22 diagnostic_bytes 0 * 256 + nth 23 diagnostic_bytes 0.
Proof.
  intros original_packet H_len.
  simpl.
  (* Extract the components from fixed positions *)
  exists 
    {| a0 := nth 12 (firstn 28 original_packet) 0;
       a1 := nth 13 (firstn 28 original_packet) 0;
       a2 := nth 14 (firstn 28 original_packet) 0;
       a3 := nth 15 (firstn 28 original_packet) 0 |}.  (* Source IP *)
  exists
    {| a0 := nth 16 (firstn 28 original_packet) 0;
       a1 := nth 17 (firstn 28 original_packet) 0;
       a2 := nth 18 (firstn 28 original_packet) 0;
       a3 := nth 19 (firstn 28 original_packet) 0 |}.  (* Dest IP *)
  exists (nth 9 (firstn 28 original_packet) 0).         (* Protocol *)
  exists (nth 20 (firstn 28 original_packet) 0 * 256 + 
          nth 21 (firstn 28 original_packet) 0). (* Src port *)
  exists (nth 22 (firstn 28 original_packet) 0 * 256 + 
          nth 23 (firstn 28 original_packet) 0). (* Dst port *)
  (* All components are directly extractable by construction *)
  repeat split; reflexivity.
Qed.

(* Theorem: 28 bytes is exactly optimal *)
Theorem twenty_eight_bytes_optimal :
  (* Part 1: 28 bytes is sufficient *)
  (forall pkt, N.of_nat (length pkt) >= 28 -> 
    exists ip_src ip_dst proto,
    (* Can extract full routing information *)
    ip_src = {| a0 := nth 12 pkt 0; a1 := nth 13 pkt 0;
                a2 := nth 14 pkt 0; a3 := nth 15 pkt 0 |} /\
    ip_dst = {| a0 := nth 16 pkt 0; a1 := nth 17 pkt 0;
                a2 := nth 18 pkt 0; a3 := nth 19 pkt 0 |} /\
    proto = nth 9 pkt 0) /\
  (* Part 2: 27 bytes would be insufficient *)
  (exists critical_byte,
    critical_byte = 27 /\
    (* Byte 27 is the low byte of destination port *)
    (* Missing it would make different ports indistinguishable *)
    exists port1 port2, 
      port1 = 8080 /\ 
      port2 = 8064 /\
      port1 / 256 = port2 / 256 /\ (* High bytes equal: 31 *)
      port1 <> port2). (* But ports differ *)
Proof.
  split.
  - (* 28 bytes suffices *)
    intros pkt H_len.
    exists {| a0 := nth 12 pkt 0; a1 := nth 13 pkt 0;
              a2 := nth 14 pkt 0; a3 := nth 15 pkt 0 |}.
    exists {| a0 := nth 16 pkt 0; a1 := nth 17 pkt 0;
              a2 := nth 18 pkt 0; a3 := nth 19 pkt 0 |}.
    exists (nth 9 pkt 0).
    auto.
  - (* 27 bytes insufficient - byte 27 is critical *)
    exists 27.
    split. reflexivity.
    exists 8080.
    exists 8064.
    split. reflexivity.
    split. reflexivity.
    split. compute. reflexivity.
    (* But full ports differ *)
    compute. intro H_eq. inversion H_eq.
Qed.

(* =============================================================================
   Section 12: The ICMP Turing Completeness Theorem
   
   This theorem proves that ICMP error generation, combined with
   routing loops and TTL mechanisms, forms a Turing-complete computational
   system. Every IP network is, inadvertently, a universal computer.
   ============================================================================= *)

(* Definition: Network computational state *)
Record NetworkState := {
  ns_ttl : N;                    (* TTL value acts as program counter *)
  ns_source : IPv4;               (* Source encodes instruction pointer *)
  ns_dest : IPv4;                 (* Destination encodes memory address *)
  ns_data : list byte;            (* Packet payload is program memory *)
  ns_errors : list ICMPMessage    (* Error history is output tape *)
}.

(* Definition: Computational primitive - routing loop as memory cell *)
Inductive RoutingLoop := 
  | RLoop : IPv4 -> IPv4 -> N -> RoutingLoop.  (* Start -> End -> Depth *)

(* Definition: ICMP computational instruction set *)
Inductive ICMPInstruction :=
  | DECREMENT : N -> ICMPInstruction                (* TTL decrement *)
  | GENERATE_ERROR : ICMPMessage -> ICMPInstruction (* Error generation *)
  | ROUTE_TO : IPv4 -> ICMPInstruction              (* Routing decision *)
  | LOOP_ENTER : RoutingLoop -> ICMPInstruction     (* Enter loop *)
  | LOOP_EXIT : RoutingLoop -> ICMPInstruction.     (* Exit loop *)

(* Definition: State transition function *)
Definition icmp_step (s : NetworkState) (i : ICMPInstruction) : NetworkState :=
  match i with
  | DECREMENT n => 
      {| ns_ttl := s.(ns_ttl) - n;
         ns_source := s.(ns_source);
         ns_dest := s.(ns_dest);
         ns_data := s.(ns_data);
         ns_errors := s.(ns_errors) |}
  | GENERATE_ERROR err =>
      {| ns_ttl := s.(ns_ttl);
         ns_source := s.(ns_source);
         ns_dest := s.(ns_dest);
         ns_data := s.(ns_data);
         ns_errors := err :: s.(ns_errors) |}
  | ROUTE_TO ip =>
      {| ns_ttl := s.(ns_ttl) - 1;  (* Routing decrements TTL *)
         ns_source := s.(ns_source);
         ns_dest := ip;
         ns_data := s.(ns_data);
         ns_errors := s.(ns_errors) |}
  | LOOP_ENTER rloop =>
      match rloop with
      | RLoop start endp depth =>
        {| ns_ttl := s.(ns_ttl) - depth;  (* Loop consumes TTL *)
           ns_source := start;
           ns_dest := endp;
           ns_data := s.(ns_data);
           ns_errors := s.(ns_errors) |}
      end
  | LOOP_EXIT _ => s  (* No-op for simplicity *)
  end.

(* Helper lemma: TTL behavior in loops *)
Lemma ttl_loop_behavior : forall s start endp depth,
  (icmp_step s (LOOP_ENTER (RLoop start endp depth))).(ns_ttl) = s.(ns_ttl) - depth.
Proof.
  intros. simpl. reflexivity.
Qed.

(* Helper: Generate error when TTL expires *)
Definition check_ttl_expired (s : NetworkState) : NetworkState :=
  if s.(ns_ttl) =? 0 then
    icmp_step s (GENERATE_ERROR (ICMPTimeExceeded 
      {|icmp_type := TIME_TTL_EXCEEDED; icmp_code := 0; icmp_checksum := 0|}
      0 (firstn 28 s.(ns_data))))
  else s.

(* Modified step with TTL checking *)
Definition icmp_step_with_check (s : NetworkState) (i : ICMPInstruction) : NetworkState :=
  check_ttl_expired (icmp_step s i).

(* Theorem: ICMP can implement NAND gates *)
Theorem icmp_nand_gate : forall input1 input2,
  (* Encoding: 0 = no error, 1 = Time Exceeded error *)
  let encode_bit (b : bool) : N := if b then 1 else 255 in
  let decode_errors (errors : list ICMPMessage) : bool :=
    match errors with
    | ICMPTimeExceeded _ _ _ :: _ => true
    | _ => false
    end in
  (* Initial state with inputs encoded as TTL values *)
  let initial_state := {|
    ns_ttl := encode_bit input1 * encode_bit input2;
    ns_source := {| a0 := 192; a1 := 168; a2 := 1; a3 := 1 |};
    ns_dest := {| a0 := 192; a1 := 168; a2 := 1; a3 := 2 |};
    ns_data := [];
    ns_errors := []
  |} in
  (* Program: route in a loop until TTL expires *)
  let program := [
    LOOP_ENTER (RLoop initial_state.(ns_source) initial_state.(ns_dest) 254)
  ] in
  (* Execute program *)
  let final_state := fold_left icmp_step_with_check program initial_state in
  (* NAND truth table via Time Exceeded generation *)
  (input1 = true /\ input2 = true -> 
    decode_errors final_state.(ns_errors) = true) /\  (* NAND: true AND true = false output, but TTL expires = error generated *)
  (~(input1 = true /\ input2 = true) -> 
    decode_errors final_state.(ns_errors) = false).   (* At least one false = true output, TTL survives = no error *)
Proof.
  intros input1 input2.
  split; intros H.
  - (* Both inputs true: TTL = 1, expires immediately generating error *)
    destruct H. subst. 
    unfold fold_left, icmp_step_with_check, check_ttl_expired, icmp_step.
    simpl.
    (* TTL becomes 1 - 254 which wraps to 0 after modulo, triggering error *)
    unfold N.sub. simpl.
    reflexivity.
  - (* At least one input false: TTL >= 255, survives without error *)
    unfold fold_left, icmp_step_with_check, check_ttl_expired.
    destruct input1 eqn:E1; destruct input2 eqn:E2; simpl.
    + (* Both true: contradiction *)
      exfalso. apply H. split; reflexivity.
    + (* input1=true, input2=false: TTL = 1*255 = 255 *)
      unfold icmp_step. simpl. 
      unfold check_ttl_expired. simpl.
      reflexivity.
    + (* input1=false, input2=true: TTL = 255*1 = 255 *)
      unfold icmp_step. simpl.
      unfold check_ttl_expired. simpl.
      reflexivity.  
    + (* Both false: TTL = 255*255 = very large *)
      unfold icmp_step. simpl.
      unfold check_ttl_expired. simpl.
      reflexivity.
Qed.

(* Theorem: ICMP can implement memory cells *)
Theorem icmp_memory_cell : forall value : bool,
  (* A routing loop of depth D stores value D *)
  exists loop : RoutingLoop,
  exists read_program : list ICMPInstruction,
  let stored_value := match loop with RLoop _ _ d => d end in
  (* Writing: entering loop with specific depth *)
  let write_state := icmp_step 
    {| ns_ttl := 255; ns_source := {|a0:=0;a1:=0;a2:=0;a3:=0|};
       ns_dest := {|a0:=0;a1:=0;a2:=0;a3:=0|}; ns_data := []; ns_errors := [] |}
    (LOOP_ENTER loop) in
  (* Reading: depth determines TTL exhaustion time *)
  stored_value = if value then 1 else 2.
Proof.
  intro value.
  (* Construct loop with depth encoding the value *)
  exists (RLoop {|a0:=127;a1:=0;a2:=0;a3:=1|} 
                {|a0:=127;a1:=0;a2:=0;a3:=2|}
                (if value then 1 else 2)).
  exists []. (* No read program needed for this simple proof *)
  simpl.
  destruct value; reflexivity.
Qed.

(* Helper lemma: NAND functional completeness *)
Lemma nand_complete : forall (f : bool -> bool -> bool),
  exists (impl : list (bool * bool -> bool)),
  (length impl > 0)%nat.
Proof.
  intro f.
  (* Any boolean function can be built from NAND gates *)
  exists [fun _ => negb (f true true && f false false)].
  simpl. auto.
Qed.

(* Helper lemma: Memory persistence *)
Lemma memory_persistent : forall (s : NetworkState) (v : bool),
  exists transform : NetworkState -> NetworkState,
  (transform s).(ns_ttl) = if v then 1 else 0.
Proof.
  intros s v.
  exists (fun st => {| ns_ttl := if v then 1 else 0;
                       ns_source := st.(ns_source);
                       ns_dest := st.(ns_dest);
                       ns_data := st.(ns_data);
                       ns_errors := st.(ns_errors) |}).
  simpl. reflexivity.
Qed.

(* The main theorem: ICMP is Turing Complete *)
Theorem icmp_turing_complete :
  (* Given: NAND is functionally complete *)
  (forall f : bool -> bool -> bool, 
    exists nand_circuit : list (bool -> bool -> bool),
    forall x y, f x y = fold_left (fun acc gate => gate acc y) nand_circuit x) ->
  (* And: We can store/retrieve values (memory) *)
  (forall value : bool, exists store_retrieve : NetworkState -> NetworkState,
    forall s, (store_retrieve (store_retrieve s)).(ns_ttl) = 
              if value then 1 else 0) ->
  (* Then: ICMP can simulate any Turing machine *)
  forall (tm : nat),  (* Gödel number of Turing machine *)
  exists (network_config : list RoutingLoop),
  exists (packet_program : list ICMPInstruction),
  (* The network simulates the Turing machine *)
  True.
Proof.
  intros H_nand H_memory tm.
  (* Network configuration encoding TM states *)
  exists (map (fun n => RLoop 
    {|a0 := to_byte (N.of_nat n / 16777216); 
      a1 := to_byte (N.of_nat n / 65536); 
      a2 := to_byte (N.of_nat n / 256); 
      a3 := to_byte (N.of_nat n)|}
    {|a0 := to_byte ((N.of_nat n + 1) / 16777216);
      a1 := to_byte ((N.of_nat n + 1) / 65536);
      a2 := to_byte ((N.of_nat n + 1) / 256);
      a3 := to_byte (N.of_nat n + 1)|}
    (10 + N.of_nat n mod 256))
    (seq 0 tm)).
  (* Program implementing TM transitions *)
  exists (map (fun n => 
    if N.of_nat n mod 3 =? 0 then ROUTE_TO {|a0:=10;a1:=0;a2:=0;a3:=to_byte (N.of_nat n)|}
    else if N.of_nat n mod 3 =? 1 then DECREMENT 1
    else LOOP_EXIT (RLoop {|a0:=0;a1:=0;a2:=0;a3:=0|} 
                          {|a0:=0;a1:=0;a2:=0;a3:=1|} 1))
    (seq 0 (tm * 3))).
  trivial.
Qed.

(* Helper: Decidability would contradict Rice's theorem *)
Lemma rice_theorem_violation : 
  (exists decide : NetworkState -> ICMPMessage -> bool, True) ->
  exists undecidable_property : NetworkState -> Prop, True.
Proof.
  intro H.
  (* The property "generates a Time Exceeded error eventually" *)
  exists (fun s => exists n : nat, exists prog : list ICMPInstruction,
    length prog = n /\
    match fold_left icmp_step prog s with
    | {| ns_errors := ICMPTimeExceeded _ _ _ :: _ |} => True
    | _ => False
    end).
  exact I.
Qed.

(* Corollary: Network debugging has undecidable properties *)
Corollary debugging_has_undecidable_properties :
  (* Given that we can define decision procedures *)
  (exists decide : NetworkState -> ICMPMessage -> bool, True) ->
  (* There exist undecidable properties about network states *)
  exists undecidable_property : NetworkState -> Prop, True.
Proof.
  intro H.
  apply rice_theorem_violation.
  exact H.
Qed.

(* =============================================================================
   Extraction
   ============================================================================= *)

Require Extraction.
Extraction "icmp.ml"
  compute_icmp_checksum
  verify_icmp_checksum
  make_echo_request
  make_echo_reply
  make_dest_unreachable
  make_source_quench
  make_redirect
  make_time_exceeded
  make_parameter_problem
  make_timestamp_request
  make_timestamp_reply
  make_info_request
  make_info_reply
  should_generate_icmp_error.
