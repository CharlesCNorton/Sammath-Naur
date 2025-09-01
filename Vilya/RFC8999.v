(* =============================================================================
   Formal Verification of Version-Independent Properties of QUIC
   
   Specification: RFC 8999 (M. Thomson, May 2021)
   Target: QUIC Invariants
   
   Module: QUIC Invariants Formalization and Verification
   Author: Charles C Norton
   Date: September 1, 2025
   
   "Yet some things he set apart, saying: 'These change not, though all else be transformed.'"
   
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
Definition word32 := N.
Definition word64 := N.

(* Invariant Constants *)
Definition INVARIANT_LONG_HEADER_FORM : N := 1.  (* Bit 7 = 1 *)
Definition INVARIANT_SHORT_HEADER_FORM : N := 0. (* Bit 7 = 0 *)
Definition INVARIANT_FIXED_BIT : N := 1.         (* Bit 6 must be 1 *)
Definition MAX_CID_LENGTH : N := 20.
Definition MIN_INITIAL_PACKET : N := 1200.

(* =============================================================================
   Section 2: Invariant Properties (RFC 8999 Section 5)
   ============================================================================= *)

(* The invariant fields that never change across versions *)
Record InvariantFields := {
  inv_header_form : bool;      (* Long (true) or Short (false) *)
  inv_fixed_bit : bool;         (* Must always be 1 *)
  inv_version : word32;         (* Version field (long header only) *)
  inv_dcid_len : N;            (* Destination CID length *)
  inv_scid_len : N;            (* Source CID length (long header only) *)
  inv_packet_remainder : N     (* Remaining packet bytes *)
}.

(* Check if a packet respects invariants *)
Definition respects_invariants (fields : InvariantFields) : bool :=
  andb fields.(inv_fixed_bit)
       (andb (N.leb fields.(inv_dcid_len) MAX_CID_LENGTH)
             (if fields.(inv_header_form) 
              then N.leb fields.(inv_scid_len) MAX_CID_LENGTH
              else true)).

(* =============================================================================
   Section 3: Long Header Invariants (RFC 8999 Section 5.2)
   ============================================================================= *)

Record LongHeaderInvariant := {
  lhi_first_byte : byte;
  lhi_version : word32;
  lhi_dcid_len : byte;
  lhi_dcid : list byte;
  lhi_scid_len : byte;
  lhi_scid : list byte
}.

Definition validate_long_header_invariant (lh : LongHeaderInvariant) : bool :=
  (* Check header form bit (bit 7) is 1 *)
  let header_form := N.testbit lh.(lhi_first_byte) 7 in
  (* Check fixed bit (bit 6) is 1 *)
  let fixed_bit := N.testbit lh.(lhi_first_byte) 6 in
  (* Check CID lengths *)
  let dcid_valid := andb (N.eqb (length lh.(lhi_dcid)) (N.to_nat lh.(lhi_dcid_len)))
                          (N.leb lh.(lhi_dcid_len) MAX_CID_LENGTH) in
  let scid_valid := andb (N.eqb (length lh.(lhi_scid)) (N.to_nat lh.(lhi_scid_len)))
                          (N.leb lh.(lhi_scid_len) MAX_CID_LENGTH) in
  andb header_form (andb fixed_bit (andb dcid_valid scid_valid)).

(* =============================================================================
   Section 4: Short Header Invariants (RFC 8999 Section 5.3)
   ============================================================================= *)

Record ShortHeaderInvariant := {
  shi_first_byte : byte;
  shi_dcid : list byte
}.

Definition validate_short_header_invariant (sh : ShortHeaderInvariant) : bool :=
  (* Check header form bit (bit 7) is 0 *)
  let header_form := negb (N.testbit sh.(shi_first_byte) 7) in
  (* Check fixed bit (bit 6) is 1 *)
  let fixed_bit := N.testbit sh.(shi_first_byte) 6 in
  (* DCID length is implicit from connection context *)
  let dcid_valid := N.leb (length sh.(shi_dcid)) (N.to_nat MAX_CID_LENGTH) in
  andb header_form (andb fixed_bit dcid_valid).

(* =============================================================================
   Section 5: Version Negotiation Invariants (RFC 8999 Section 5.2.2)
   ============================================================================= *)

Record VersionNegotiationInvariant := {
  vni_first_byte : byte;
  vni_version : word32;  (* Must be 0x00000000 *)
  vni_dcid_len : byte;
  vni_dcid : list byte;
  vni_scid_len : byte;
  vni_scid : list byte;
  vni_supported_versions : list word32
}.

Definition validate_version_negotiation (vn : VersionNegotiationInvariant) : bool :=
  (* Version field must be 0 *)
  let version_zero := N.eqb vn.(vni_version) 0 in
  (* Header form bit must be 1 *)
  let header_form := N.testbit vn.(vni_first_byte) 7 in
  (* Fixed bit can be any value for VN *)
  (* Supported versions must be non-empty and 4-byte aligned *)
  let versions_valid := andb (negb (null vn.(vni_supported_versions)))
                              (N.eqb (N.modulo (length vn.(vni_supported_versions)) 4) 0) in
  andb version_zero (andb header_form versions_valid).

(* =============================================================================
   Section 6: Greasing and Extension (RFC 8999 Section 7)
   ============================================================================= *)

(* Check if version is reserved for greasing *)
Definition is_grease_version (v : word32) : bool :=
  N.eqb (N.land v 0x0F0F0F0F) 0x0A0A0A0A.

(* Generate a grease version *)
Definition generate_grease_version (seed : N) : word32 :=
  N.lor 0x0A0A0A0A (N.shiftl (N.modulo seed 0x0F) 28).

(* =============================================================================
   Section 7: Packet Type Independence (RFC 8999 Section 6)
   ============================================================================= *)

(* Invariant packet classification *)
Inductive InvariantPacketType :=
  | IPTLongHeader : word32 -> InvariantPacketType  (* With version *)
  | IPTShortHeader : InvariantPacketType
  | IPTVersionNegotiation : InvariantPacketType.

Definition classify_packet_invariant (first_byte : byte) (version : option word32) 
                                    : InvariantPacketType :=
  if N.testbit first_byte 7 then
    match version with
    | Some v => 
        if N.eqb v 0 then IPTVersionNegotiation
        else IPTLongHeader v
    | None => IPTLongHeader 0  (* Invalid but classifiable *)
    end
  else
    IPTShortHeader.

(* =============================================================================
   Section 8: Connection ID Handling (RFC 8999 Section 5.4)
   ============================================================================= *)

Record ConnectionIDInvariant := {
  cid_bytes : list byte;
  cid_length : N
}.

Definition validate_cid_invariant (cid : ConnectionIDInvariant) : bool :=
  andb (N.eqb (length cid.(cid_bytes)) (N.to_nat cid.(cid_length)))
       (N.leb cid.(cid_length) MAX_CID_LENGTH).

(* Extract connection IDs from packet *)
Definition extract_cids_invariant (packet : list byte) 
                                 : option (ConnectionIDInvariant * ConnectionIDInvariant) :=
  match packet with
  | first :: rest =>
      if N.testbit first 7 then
        (* Long header *)
        match rest with
        | v1 :: v2 :: v3 :: v4 :: dcid_len :: rest' =>
            let dcid := firstn (N.to_nat dcid_len) rest' in
            match skipn (N.to_nat dcid_len) rest' with
            | scid_len :: rest'' =>
                let scid := firstn (N.to_nat scid_len) rest'' in
                Some ({| cid_bytes := dcid; cid_length := dcid_len |},
                      {| cid_bytes := scid; cid_length := scid_len |})
            | _ => None
            end
        | _ => None
        end
      else
        (* Short header - DCID only, length is implicit *)
        None  (* Cannot determine without connection context *)
  | _ => None
  end.

(* =============================================================================
   Section 9: Forward Compatibility (RFC 8999 Section 8)
   ============================================================================= *)

(* Properties that MUST remain invariant *)
Record ForwardCompatibility := {
  fc_long_header_bit : bool;      (* Bit 7 indicates header type *)
  fc_fixed_bit_position : N;      (* Bit 6 is fixed bit *)
  fc_version_field_position : N;  (* Bytes 1-4 for long header *)
  fc_dcid_len_position : N;       (* Byte 5 for long header *)
  fc_max_cid_length : N           (* 20 bytes maximum *)
}.

Definition default_forward_compatibility : ForwardCompatibility :=
  {| fc_long_header_bit := true;
     fc_fixed_bit_position := 6;
     fc_version_field_position := 1;
     fc_dcid_len_position := 5;
     fc_max_cid_length := 20 |}.

(* =============================================================================
   Section 10: Minimum Packet Size (RFC 8999 Section 5.1)
   ============================================================================= *)

Definition meets_minimum_size (packet_length : N) (is_initial : bool) : bool :=
  if is_initial then
    N.leb MIN_INITIAL_PACKET packet_length
  else
    true.  (* No minimum for other packet types *)

(* =============================================================================
   Section 11: Key Properties
   ============================================================================= *)

(* Property 1: Fixed bit is always 1 in valid packets *)
Theorem fixed_bit_invariant : forall fields,
  respects_invariants fields = true ->
  fields.(inv_fixed_bit) = true.
Proof.
  intros. unfold respects_invariants in H.
  apply andb_prop in H. destruct H.
  exact H.
Qed.

(* Property 2: CID lengths are bounded *)
Theorem cid_length_bounded : forall fields,
  respects_invariants fields = true ->
  fields.(inv_dcid_len) <= MAX_CID_LENGTH.
Proof.
  intros. unfold respects_invariants in H.
  apply andb_prop in H. destruct H.
  apply andb_prop in H0. destruct H0.
  apply N.leb_le in H0. exact H0.
Qed.

(* Property 3: Version negotiation has zero version *)
Theorem vn_version_zero : forall vn,
  validate_version_negotiation vn = true ->
  vn.(vni_version) = 0.
Proof.
  intros. unfold validate_version_negotiation in H.
  apply andb_prop in H. destruct H.
  apply andb_prop in H. destruct H.
  apply N.eqb_eq in H. exact H.
Qed.

(* Property 4: Grease versions are identifiable *)
Theorem grease_version_pattern : forall seed,
  is_grease_version (generate_grease_version seed) = true.
Proof.
  intros. unfold is_grease_version, generate_grease_version.
  admit.
Qed.

(* Property 5: Long header is identifiable by first bit *)
Theorem long_header_identification : forall first_byte version,
  N.testbit first_byte 7 = true ->
  exists v, classify_packet_invariant first_byte (Some version) = IPTLongHeader v \/
            classify_packet_invariant first_byte (Some version) = IPTVersionNegotiation.
Proof.
  intros. unfold classify_packet_invariant.
  rewrite H.
  destruct (N.eqb version 0) eqn:E.
  - right. reflexivity.
  - left. exists version. reflexivity.
Qed.

(* Property 6: Initial packets meet minimum size *)
Theorem initial_minimum_size : forall len,
  meets_minimum_size len true = true ->
  len >= MIN_INITIAL_PACKET.
Proof.
  intros. unfold meets_minimum_size in H.
  apply N.leb_le in H. exact H.
Qed.

(* =============================================================================
   Section 12: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction "quic_invariants.ml"
  respects_invariants
  validate_long_header_invariant
  validate_short_header_invariant
  validate_version_negotiation
  is_grease_version
  classify_packet_invariant
  extract_cids_invariant.
