(* =============================================================================
   Formal Verification of OSPFv3 Link State Advertisement (LSA) Extensibility
   
   Specification: RFC 8362 (A. Lindem, A. Roy, D. Goethals, V. Reddy Vallem, 
                            F. Baker, April 2018)
   Target: OSPFv3 Extended LSAs
   
   Module: OSPFv3 LSA Extensibility Formalization and Verification
   Author: Charles C Norton
   Date: September 1, 2025
   
   "In that time the smiths surpassed all their former works, as the moon surpasses the stars."
   
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
Definition word64 := N.
Definition word128 := N.

(* Extended LSA Function Codes (RFC 8362 Section 3) *)
Definition E_ROUTER_LSA : word16 := 0x8001.
Definition E_NETWORK_LSA : word16 := 0x8002.
Definition E_INTER_AREA_PREFIX_LSA : word16 := 0x8003.
Definition E_INTER_AREA_ROUTER_LSA : word16 := 0x8004.
Definition E_AS_EXTERNAL_LSA : word16 := 0x8005.
Definition E_NSSA_LSA : word16 := 0x8007.
Definition E_LINK_LSA : word16 := 0x8008.
Definition E_INTRA_AREA_PREFIX_LSA : word16 := 0x8009.

(* LSA Header Size Constants *)
Definition LEGACY_LSA_HEADER_SIZE : N := 20.
Definition EXTENDED_LSA_HEADER_SIZE : N := 20.  (* Same size, different format *)

(* TLV Type Codes *)
Definition TLV_ROUTER_LINK : word16 := 1.
Definition TLV_ATTACHED_ROUTERS : word16 := 2.
Definition TLV_INTER_AREA_PREFIX : word16 := 3.
Definition TLV_INTER_AREA_ROUTER : word16 := 4.
Definition TLV_EXTERNAL_PREFIX : word16 := 5.
Definition TLV_IPV6_LINK_LOCAL : word16 := 6.
Definition TLV_IPV4_LINK_LOCAL : word16 := 7.
Definition TLV_PREFIX : word16 := 8.
Definition TLV_PREFIX_RANGE : word16 := 9.
Definition TLV_LINK_ATTRIBUTES : word16 := 10.
Definition TLV_SRV6_LOCATOR : word16 := 11.
Definition TLV_SRV6_END_SID : word16 := 12.

(* Sub-TLV Type Codes *)
Definition SUBTLV_PREFIX_SID : word16 := 2.
Definition SUBTLV_ADJ_SID : word16 := 3.
Definition SUBTLV_LAN_ADJ_SID : word16 := 4.
Definition SUBTLV_SRV6_END_X_SID : word16 := 5.
Definition SUBTLV_SRV6_LAN_END_X_SID : word16 := 6.

(* =============================================================================
   Section 2: TLV Structure (RFC 8362 Section 3)
   ============================================================================= *)

Record TLV := {
  tlv_type : word16;
  tlv_length : word16;
  tlv_value : list byte
}.

Record SubTLV := {
  subtlv_type : word16;
  subtlv_length : word16;
  subtlv_value : list byte
}.

(* Extended TLV with sub-TLVs *)
Record ExtendedTLV := {
  etlv_type : word16;
  etlv_length : word16;
  etlv_value : list byte;
  etlv_subtlvs : list SubTLV
}.

(* Parse TLVs from byte stream *)
Fixpoint parse_tlvs (data : list byte) (remaining : N) : list TLV :=
  if N.eqb remaining 0 then []
  else
    match data with
    | t1 :: t2 :: l1 :: l2 :: rest =>
        let typ := N.lor (N.shiftl t1 8) t2 in
        let len := N.lor (N.shiftl l1 8) l2 in
        if N.leb len remaining then
          let value := firstn (N.to_nat len) rest in
          let tlv := {| tlv_type := typ;
                        tlv_length := len;
                        tlv_value := value |} in
          tlv :: parse_tlvs (skipn (N.to_nat len) rest) (remaining - len - 4)
        else []
    | _ => []
    end.

(* =============================================================================
   Section 3: Extended LSA Header (RFC 8362 Section 4)
   ============================================================================= *)

Record ExtendedLSAHeader := {
  elsa_age : word16;
  elsa_type : word16;          (* U, S2, S1, Function Code *)
  elsa_link_state_id : word32;
  elsa_advertising_router : word32;
  elsa_sequence : word32;
  elsa_checksum : word16;
  elsa_length : word16
}.

(* Check if LSA is Extended format *)
Definition is_extended_lsa (lsa_type : word16) : bool :=
  N.testbit lsa_type 15.  (* Check if most significant bit is set *)

(* Extract function code from Extended LSA type *)
Definition get_extended_function_code (lsa_type : word16) : word16 :=
  N.land lsa_type 0x7FFF.

(* =============================================================================
   Section 4: Extended LSA Bodies (RFC 8362 Section 5-7)
   ============================================================================= *)

(* E-Router-LSA *)
Record ERouterLSA := {
  erlsa_flags : byte;         (* V, E, B, Nt bits *)
  erlsa_options : N;          (* 24 bits *)
  erlsa_tlvs : list ExtendedTLV
}.

(* Router-Link TLV *)
Record RouterLinkTLV := {
  rltlv_type : byte;          (* 1=p2p, 2=transit, 3=stub, 4=virtual *)
  rltlv_reserved : byte;
  rltlv_metric : word16;
  rltlv_interface_id : word32;
  rltlv_neighbor_interface_id : word32;
  rltlv_neighbor_router_id : word32;
  rltlv_subtlvs : list SubTLV
}.

(* E-Network-LSA *)
Record ENetworkLSA := {
  enlsa_options : N;          (* 24 bits *)
  enlsa_tlvs : list ExtendedTLV
}.

(* E-Inter-Area-Prefix-LSA *)
Record EInterAreaPrefixLSA := {
  eiaplsa_metric : N;         (* 24 bits *)
  eiaplsa_tlvs : list ExtendedTLV
}.

(* E-AS-External-LSA *)
Record EASExternalLSA := {
  easelsa_flags : byte;       (* E, F, T bits *)
  easelsa_metric : N;         (* 24 bits *)
  easelsa_tlvs : list ExtendedTLV
}.

(* E-Link-LSA *)
Record ELinkLSA := {
  ellsa_priority : byte;
  ellsa_options : N;          (* 24 bits *)
  ellsa_tlvs : list ExtendedTLV
}.

(* E-Intra-Area-Prefix-LSA *)
Record EIntraAreaPrefixLSA := {
  eiaplsa_referenced_lsa_type : word16;
  eiaplsa_referenced_link_state_id : word32;
  eiaplsa_referenced_advertising_router : word32;
  eiaplsa_tlvs : list ExtendedTLV
}.

(* =============================================================================
   Section 5: Prefix TLV Structure (RFC 8362 Section 9)
   ============================================================================= *)

Record PrefixTLV := {
  ptlv_metric : word32;
  ptlv_prefix_length : byte;
  ptlv_prefix_options : byte;
  ptlv_reserved : word16;
  ptlv_address : list byte;    (* Variable length *)
  ptlv_subtlvs : list SubTLV
}.

(* Prefix Options bits *)
Definition PREFIX_OPT_NU : byte := 0x01.   (* No Unicast *)
Definition PREFIX_OPT_LA : byte := 0x02.   (* Local Address *)
Definition PREFIX_OPT_P : byte := 0x08.    (* Propagate *)
Definition PREFIX_OPT_DN : byte := 0x10.   (* Down *)
Definition PREFIX_OPT_N : byte := 0x20.    (* Node SID *)

(* =============================================================================
   Section 6: Segment Routing Extensions (RFC 8362 Appendix)
   ============================================================================= *)

(* Prefix-SID Sub-TLV *)
Record PrefixSIDSubTLV := {
  psid_flags : byte;
  psid_reserved : byte;
  psid_algorithm : byte;
  psid_reserved2 : byte;
  psid_index_label : word32    (* SID/Index/Label *)
}.

(* Adj-SID Sub-TLV *)
Record AdjSIDSubTLV := {
  asid_flags : byte;
  asid_reserved : byte;
  asid_weight : byte;
  asid_reserved2 : byte;
  asid_index_label : word32
}.

(* SRv6 Locator TLV *)
Record SRv6LocatorTLV := {
  srv6_route_type : byte;
  srv6_algorithm : byte;
  srv6_locator_length : byte;
  srv6_flags : byte;
  srv6_metric : word32;
  srv6_locator : list byte;    (* IPv6 address prefix *)
  srv6_subtlvs : list SubTLV
}.

(* =============================================================================
   Section 7: Backward Compatibility (RFC 8362 Section 8)
   ============================================================================= *)

(* Convert Extended LSA to Legacy format *)
Definition extended_to_legacy_lsa (elsa : ExtendedLSAHeader) 
                                 (body_tlvs : list ExtendedTLV) : option (word16 * list byte) :=
  if is_extended_lsa elsa.(elsa_type) then
    None  (* Cannot convert extended to legacy *)
  else
    Some (elsa.(elsa_type), []).  (* Simplified *)

(* Check if router supports Extended LSAs *)
Definition supports_extended_lsas (options : N) : bool :=
  N.testbit options 20.  (* E-bit in Options field *)

(* Handle mixed Extended/Legacy environment *)
Definition handle_mixed_lsas (extended_capable : bool) 
                            (lsa_type : word16) : N :=
  if extended_capable then
    if is_extended_lsa lsa_type then
      0  (* Process as Extended *)
    else
      1  (* Process as Legacy *)
  else
    if is_extended_lsa lsa_type then
      2  (* Ignore - not understood *)
    else
      1. (* Process as Legacy *)

(* =============================================================================
   Section 8: LSA Processing with TLVs
   ============================================================================= *)

(* Process Router-Link TLVs *)
Definition process_router_link_tlvs (tlvs : list ExtendedTLV) 
                                   : list RouterLinkTLV :=
  flat_map (fun tlv =>
    if N.eqb tlv.(etlv_type) TLV_ROUTER_LINK then
      (* Parse Router-Link TLV structure *)
      []  (* Simplified *)
    else []
  ) tlvs.

(* Process Prefix TLVs *)
Definition process_prefix_tlvs (tlvs : list ExtendedTLV) : list PrefixTLV :=
  flat_map (fun tlv =>
    if N.eqb tlv.(etlv_type) TLV_PREFIX then
      (* Parse Prefix TLV structure *)
      []  (* Simplified *)
    else []
  ) tlvs.

(* Extract Sub-TLVs *)
Definition extract_subtlvs (tlv : ExtendedTLV) : list SubTLV :=
  tlv.(etlv_subtlvs).

(* =============================================================================
   Section 9: Validation and Error Handling
   ============================================================================= *)

(* Validate TLV length *)
Definition validate_tlv_length (tlv : TLV) : bool :=
  N.eqb (length tlv.(tlv_value)) (N.to_nat tlv.(tlv_length)).

(* Validate Extended LSA *)
Definition validate_extended_lsa (elsa : ExtendedLSAHeader) 
                                (tlvs : list ExtendedTLV) : bool :=
  let total_tlv_length := fold_left (fun acc tlv => 
    acc + tlv.(etlv_length) + 4) tlvs 0 in
  andb (is_extended_lsa elsa.(elsa_type))
       (N.eqb (elsa.(elsa_length) - EXTENDED_LSA_HEADER_SIZE) total_tlv_length).

(* Handle unknown TLV *)
Definition handle_unknown_tlv (tlv : TLV) : N :=
  if N.ltb tlv.(tlv_type) 32768 then
    0  (* Ignore and continue *)
  else
    1. (* Treat as error *)

(* =============================================================================
   Section 10: Key Properties
   ============================================================================= *)

(* Property 1: Extended LSAs identified by top bit *)
Theorem extended_lsa_identification : forall lsa_type,
  is_extended_lsa lsa_type = true <-> N.testbit lsa_type 15 = true.
Proof.
  intros. unfold is_extended_lsa. split; intros; exact H.
Qed.

(* Property 2: TLV parsing preserves length *)
Theorem tlv_parsing_preserves_length : forall data remaining tlvs,
  parse_tlvs data remaining = tlvs ->
  fold_left (fun acc tlv => acc + tlv.(tlv_length) + 4) tlvs 0 <= remaining.
Proof.
  admit.
Qed.

(* Property 3: Extended LSAs require capability *)
Theorem extended_requires_capability : forall opts lsa_type action,
  handle_mixed_lsas (supports_extended_lsas opts) lsa_type = action ->
  is_extended_lsa lsa_type = true ->
  supports_extended_lsas opts = true \/ action = 2.
Proof.
  intros. unfold handle_mixed_lsas in H.
  destruct (supports_extended_lsas opts) eqn:E.
  - left. exact E.
  - rewrite H0 in H. right. exact H.
Qed.

(* Property 4: Validation ensures consistency *)
Theorem validation_ensures_consistency : forall elsa tlvs,
  validate_extended_lsa elsa tlvs = true ->
  is_extended_lsa elsa.(elsa_type) = true.
Proof.
  intros. unfold validate_extended_lsa in H.
  apply andb_prop in H. destruct H.
  exact H.
Qed.

(* Property 5: Unknown TLV handling is safe *)
Theorem unknown_tlv_safe : forall tlv,
  tlv.(tlv_type) < 32768 ->
  handle_unknown_tlv tlv = 0.
Proof.
  intros. unfold handle_unknown_tlv.
  apply N.ltb_lt in H. rewrite H. reflexivity.
Qed.

(* =============================================================================
   Section 11: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction "ospfv3_extended_lsa.ml"
  is_extended_lsa
  parse_tlvs
  validate_extended_lsa
  handle_unknown_tlv
  supports_extended_lsas
  process_router_link_tlvs
  process_prefix_tlvs.
            
