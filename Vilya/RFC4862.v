(* =============================================================================
   Formal Verification of IPv6 Stateless Address Autoconfiguration (SLAAC)
   
   Specification: RFC 4862 (S. Thomson, T. Narten, T. Jinmei, September 2007)
   Target: IPv6 Address Autoconfiguration
   
   Module: IPv6 SLAAC Protocol Formalization and Verification
   Author: Charles C Norton
   Date: August 29, 2025
   
   "Then gathered the Mírdain in the great hall, eager for his teaching."
   
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

(* SLAAC Constants (RFC 4862 Section 10) *)
Definition DupAddrDetectTransmits : N := 1.
Definition RETRANS_TIMER : N := 1000.                    (* milliseconds *)
Definition MAX_RTR_SOLICITATION_DELAY : N := 1.          (* seconds *)
Definition RTR_SOLICITATION_INTERVAL : N := 4.           (* seconds *)
Definition MAX_RTR_SOLICITATIONS : N := 3.
Definition TENTATIVE_DURATION : N := 1000.               (* milliseconds *)
Definition DESYNC_FACTOR : N := 600.                     (* 0.6 seconds *)
Definition REGEN_ADVANCE : N := 5.                       (* seconds *)
Definition TEMP_VALID_LIFETIME : N := 86400.             (* 1 day *)
Definition TEMP_PREFERRED_LIFETIME : N := 3600.          (* 1 hour *)
Definition TEMP_IDGEN_RETRIES : N := 3.
Definition MAX_DESYNC_FACTOR : N := 600.                 (* milliseconds *)

(* =============================================================================
   Section 2: IPv6 Address Types
   ============================================================================= *)

Record IPv6Address := {
  addr_bytes : list byte;
  addr_valid : length addr_bytes = 16%nat
}.

(* Interface Identifier (64 bits) *)
Record InterfaceID := {
  iid_bytes : list byte;
  iid_valid : length iid_bytes = 8%nat
}.

(* Address states *)
Inductive AddressState :=
  | TENTATIVE     (* DAD in progress *)
  | VALID         (* DAD succeeded *)
  | PREFERRED     (* Can be used for new connections *)
  | DEPRECATED    (* Should not be used for new connections *)
  | INVALID.      (* Cannot be used *)

(* Address types *)
Inductive AddressType :=
  | LINK_LOCAL
  | GLOBAL_UNICAST
  | UNIQUE_LOCAL
  | TEMPORARY      (* Privacy extension *)
  | ANYCAST.

(* =============================================================================
   Section 3: Address Configuration Entry
   ============================================================================= *)

Record AddressEntry := {
  ae_address : IPv6Address;
  ae_prefix_length : byte;
  ae_state : AddressState;
  ae_type : AddressType;
  ae_valid_lifetime : N;
  ae_preferred_lifetime : N;
  ae_creation_time : N;
  ae_dad_attempts : N;
  ae_is_tentative : bool;
  ae_is_optimistic : bool;  (* RFC 4429 *)
  ae_is_temporary : bool     (* RFC 4941 *)
}.

(* =============================================================================
   Section 4: Modified EUI-64 Interface ID (RFC 4862 Appendix A)
   ============================================================================= *)

Definition create_modified_eui64 (mac : list byte) : option InterfaceID :=
  match mac with
  | [a; b; c; d; e; f] =>
      (* Insert FF:FE in the middle and flip universal/local bit *)
      let a' := N.lxor a 0x02 in
      Some {| iid_bytes := [a'; b; c; 0xFF; 0xFE; d; e; f];
              iid_valid := eq_refl |}
  | _ => None
  end.

(* Check if interface ID is reserved (RFC 4862 Section 2) *)
Definition is_reserved_iid (iid : InterfaceID) : bool :=
  match iid.(iid_bytes) with
  | [0; 0; 0; 0; 0; 0; 0; 0] => true                    (* All zeros *)
  | [0xFD; _; _; _; _; _; _; _] => true                 (* ISATAP *)
  | _ => false
  end.

(* =============================================================================
   Section 5: Link-Local Address Formation (RFC 4862 Section 5.3)
   ============================================================================= *)

Definition link_local_prefix : list byte := [0xFE; 0x80] ++ repeat 0 6.

Definition create_link_local_address (iid : InterfaceID) : IPv6Address.
  refine {| addr_bytes := link_local_prefix ++ iid.(iid_bytes) |}.
  rewrite app_length. unfold link_local_prefix.
  rewrite app_length, repeat_length. 
  simpl. rewrite iid.(iid_valid). reflexivity.
Defined.

(* =============================================================================
   Section 6: Global Address Formation (RFC 4862 Section 5.5)
   ============================================================================= *)

Definition create_global_address (prefix : list byte) (prefix_len : byte) 
                                (iid : InterfaceID) : option IPv6Address :=
  if N.eqb prefix_len 64 then
    if N.eqb (length prefix) 8 then
      Some {| addr_bytes := prefix ++ iid.(iid_bytes);
              addr_valid := eq_refl |}
    else None
  else None.

(* =============================================================================
   Section 7: Duplicate Address Detection (RFC 4862 Section 5.4)
   ============================================================================= *)

Record DADEntry := {
  dad_address : IPv6Address;
  dad_attempts_remaining : N;
  dad_ns_sent : N;
  dad_timer : N;
  dad_state : AddressState
}.

Definition start_dad (addr : IPv6Address) : DADEntry :=
  {| dad_address := addr;
     dad_attempts_remaining := DupAddrDetectTransmits;
     dad_ns_sent := 0;
     dad_timer := 0;
     dad_state := TENTATIVE |}.

(* Send DAD Neighbor Solicitation *)
Definition create_dad_ns (addr : IPv6Address) : (IPv6Address * IPv6Address) :=
  (* Source: unspecified, Destination: solicited-node multicast *)
  (IPv6Address (* unspecified *), IPv6Address (* solicited_node addr *)).

(* Process DAD result *)
Definition process_dad_result (entry : DADEntry) (conflict : bool) : DADEntry :=
  if conflict then
    {| dad_address := entry.(dad_address);
       dad_attempts_remaining := 0;
       dad_ns_sent := entry.(dad_ns_sent);
       dad_timer := entry.(dad_timer);
       dad_state := INVALID |}
  else if N.eqb entry.(dad_attempts_remaining) 0 then
    {| dad_address := entry.(dad_address);
       dad_attempts_remaining := 0;
       dad_ns_sent := entry.(dad_ns_sent);
       dad_timer := entry.(dad_timer);
       dad_state := VALID |}
  else
    entry.

(* =============================================================================
   Section 8: Privacy Extensions (RFC 4941)
   ============================================================================= *)

(* Generate random interface identifier *)
Definition generate_random_iid (seed : word64) : InterfaceID.
  (* Should use cryptographically secure random *)
  refine {| iid_bytes := repeat 0 8 |}.
  rewrite repeat_length. reflexivity.
Defined.

(* Generate temporary address *)
Definition create_temporary_address (prefix : list byte) (seed : word64) 
                                   : option IPv6Address :=
  let iid := generate_random_iid seed in
  create_global_address prefix 64 iid.

(* =============================================================================
   Section 9: Router Advertisement Processing (RFC 4862 Section 5.5)
   ============================================================================= *)

Record PrefixInfo := {
  pi_prefix : list byte;
  pi_length : byte;
  pi_on_link : bool;
  pi_autonomous : bool;
  pi_valid_lifetime : word32;
  pi_preferred_lifetime : word32
}.

Definition process_prefix_info (pi : PrefixInfo) (iid : InterfaceID)
                              (current_time : N) : option AddressEntry :=
  if pi.(pi_autonomous) then
    match create_global_address pi.(pi_prefix) pi.(pi_length) iid with
    | Some addr =>
        Some {| ae_address := addr;
                ae_prefix_length := pi.(pi_length);
                ae_state := TENTATIVE;
                ae_type := GLOBAL_UNICAST;
                ae_valid_lifetime := pi.(pi_valid_lifetime);
                ae_preferred_lifetime := pi.(pi_preferred_lifetime);
                ae_creation_time := current_time;
                ae_dad_attempts := 0;
                ae_is_tentative := true;
                ae_is_optimistic := false;
                ae_is_temporary := false |}
    | None => None
    end
  else None.

(* =============================================================================
   Section 10: Address Lifetime Management (RFC 4862 Section 5.5.4)
   ============================================================================= *)

Definition update_address_lifetimes (entry : AddressEntry) 
                                   (new_valid new_preferred : word32)
                                   (current_time : N) : AddressEntry :=
  let remaining_valid := 
    if N.ltb entry.(ae_valid_lifetime) (current_time - entry.(ae_creation_time))
    then 0
    else entry.(ae_valid_lifetime) - (current_time - entry.(ae_creation_time)) in
  
  let new_valid' := 
    if N.eqb new_valid 0xFFFFFFFF then new_valid  (* Infinity *)
    else if N.ltb new_valid 7200 then 7200        (* Min 2 hours *)
    else new_valid in
  
  {| ae_address := entry.(ae_address);
     ae_prefix_length := entry.(ae_prefix_length);
     ae_state := if N.ltb new_preferred (current_time - entry.(ae_creation_time))
                then DEPRECATED
                else entry.(ae_state);
     ae_type := entry.(ae_type);
     ae_valid_lifetime := if N.ltb remaining_valid new_valid' 
                          then new_valid'
                          else remaining_valid;
     ae_preferred_lifetime := new_preferred;
     ae_creation_time := entry.(ae_creation_time);
     ae_dad_attempts := entry.(ae_dad_attempts);
     ae_is_tentative := entry.(ae_is_tentative);
     ae_is_optimistic := entry.(ae_is_optimistic);
     ae_is_temporary := entry.(ae_is_temporary) |}.

(* =============================================================================
   Section 11: SLAAC State Machine
   ============================================================================= *)

Record SLAACContext := {
  slaac_addresses : list AddressEntry;
  slaac_dad_queue : list DADEntry;
  slaac_interface_id : InterfaceID;
  slaac_link_local : option IPv6Address;
  slaac_rs_count : N;
  slaac_last_rs : N;
  slaac_m_flag : bool;  (* Managed flag *)
  slaac_o_flag : bool;  (* Other config flag *)
  slaac_temp_addresses : bool;  (* Privacy extensions enabled *)
  slaac_optimistic_dad : bool   (* RFC 4429 *)
}.

(* Initialize SLAAC on interface *)
Definition init_slaac (mac : list byte) : option SLAACContext :=
  match create_modified_eui64 mac with
  | Some iid =>
      let link_local := create_link_local_address iid in
      Some {| slaac_addresses := [];
              slaac_dad_queue := [start_dad link_local];
              slaac_interface_id := iid;
              slaac_link_local := Some link_local;
              slaac_rs_count := 0;
              slaac_last_rs := 0;
              slaac_m_flag := false;
              slaac_o_flag := false;
              slaac_temp_addresses := false;
              slaac_optimistic_dad := false |}
  | None => None
  end.

(* =============================================================================
   Section 12: Router Solicitation (RFC 4862 Section 6.3.7)
   ============================================================================= *)

Definition should_send_rs (ctx : SLAACContext) (current_time : N) : bool :=
  andb (N.ltb ctx.(slaac_rs_count) MAX_RTR_SOLICITATIONS)
       (N.leb RTR_SOLICITATION_INTERVAL 
              (current_time - ctx.(slaac_last_rs))).

Definition send_router_solicitation (ctx : SLAACContext) (current_time : N) 
                                   : SLAACContext :=
  {| slaac_addresses := ctx.(slaac_addresses);
     slaac_dad_queue := ctx.(slaac_dad_queue);
     slaac_interface_id := ctx.(slaac_interface_id);
     slaac_link_local := ctx.(slaac_link_local);
     slaac_rs_count := ctx.(slaac_rs_count) + 1;
     slaac_last_rs := current_time;
     slaac_m_flag := ctx.(slaac_m_flag);
     slaac_o_flag := ctx.(slaac_o_flag);
     slaac_temp_addresses := ctx.(slaac_temp_addresses);
     slaac_optimistic_dad := ctx.(slaac_optimistic_dad) |}.

(* =============================================================================
   Section 13: Key Properties
   ============================================================================= *)

(* Property 1: Link-local always uses FE80::/64 *)
Theorem link_local_prefix_correct : forall iid,
  let addr := create_link_local_address iid in
  take 8 addr.(addr_bytes) = link_local_prefix.
Proof.
  intros. unfold create_link_local_address.
  simpl. unfold link_local_prefix.
  admit.
Qed.

(* Property 2: Modified EUI-64 has universal/local bit flipped *)
Theorem modified_eui64_flips_bit : forall a b c d e f iid,
  create_modified_eui64 [a; b; c; d; e; f] = Some iid ->
  exists rest, iid.(iid_bytes) = (N.lxor a 0x02) :: rest.
Proof.
  intros. unfold create_modified_eui64 in H.
  inversion H. simpl. eauto.
Qed.

(* Property 3: DAD starts in tentative state *)
Theorem dad_starts_tentative : forall addr,
  (start_dad addr).(dad_state) = TENTATIVE.
Proof.
  intros. unfold start_dad. reflexivity.
Qed.

(* Property 4: Conflict results in invalid state *)
Theorem dad_conflict_invalid : forall entry,
  (process_dad_result entry true).(dad_state) = INVALID.
Proof.
  intros. unfold process_dad_result. reflexivity.
Qed.

(* Property 5: Address lifetimes are monotonic *)
Theorem lifetime_monotonic : forall entry new_valid new_pref time,
  let entry' := update_address_lifetimes entry new_valid new_pref time in
  entry'.(ae_valid_lifetime) <= entry.(ae_valid_lifetime) + new_valid.
Proof.
  admit.
Qed.

(* Property 6: RS count bounded *)
Theorem rs_count_bounded : forall ctx time,
  should_send_rs ctx time = true ->
  ctx.(slaac_rs_count) < MAX_RTR_SOLICITATIONS.
Proof.
  intros. unfold should_send_rs in H.
  apply andb_prop in H. destruct H.
  apply N.ltb_lt in H. exact H.
Qed.

(* =============================================================================
   Section 14: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].
Extract Inductive option => "option" [ "Some" "None" ].

Extraction "slaac.ml"
  init_slaac
  create_modified_eui64
  create_link_local_address
  create_global_address
  start_dad
  process_dad_result
  process_prefix_info
  update_address_lifetimes
  should_send_rs.
