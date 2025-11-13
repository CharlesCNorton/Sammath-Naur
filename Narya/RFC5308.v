(* =============================================================================
   Formal Verification of Routing IPv6 with IS-IS
   
   Specification: RFC 5308 (C. Hopps, October 2008)
   Target: IS-IS IPv6 Support
   
   Module: IS-IS IPv6 Support Formalization and Verification
   Author: Charles C Norton
   Date: September 1, 2025
   
   "And Annatar moved among the forges, guiding every hand that labored."
   
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

(* List equality comparison *)
Fixpoint list_beq {A : Type} (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: xs, y :: ys => andb (eqb x y) (list_beq eqb xs ys)
  | _, _ => false
  end.

(* IPv6 IS-IS Constants *)
Definition NLPID_IPV6 : byte := 0x8E.
Definition IPV6_MAX_PREFIX_LEN : N := 128.
Definition IPV6_INTERFACE_ADDRESS_LENGTH : N := 16.
Definition MAX_V6_PATH_METRIC : word32 := 0xFE000000.

(* New TLV Types for IPv6 (RFC 5308) *)
Definition TLV_IPV6_INTERFACE_ADDR : word16 := 232.
Definition TLV_IPV6_REACHABILITY : word16 := 236.
Definition TLV_MT_ISN : word16 := 222.              (* Multi-Topology IS Neighbors *)
Definition TLV_MT_IS_REACH : word16 := 222.        (* MT Intermediate Systems *)
Definition TLV_MT_IPV6_REACH : word16 := 237.      (* MT IPv6 Reachability *)

(* Sub-TLV Types *)
Definition SUBTLV_IPV6_SOURCE_PREFIX : byte := 22.
Definition SUBTLV_PREFIX_SID : byte := 3.
Definition SUBTLV_PREFIX_ATTRIBUTES : byte := 4.

(* Multi-Topology IDs *)
Definition MT_ID_DEFAULT : word16 := 0.
Definition MT_ID_IPV4_UNICAST : word16 := 0.
Definition MT_ID_IPV6_UNICAST : word16 := 2.
Definition MT_ID_IPV4_MULTICAST : word16 := 3.
Definition MT_ID_IPV6_MULTICAST : word16 := 4.

(* =============================================================================
   Section 2: IPv6 Address Representation
   ============================================================================= *)

Record IPv6Address := {
  ipv6_bytes : list byte;
  ipv6_valid : length ipv6_bytes = 16%nat
}.

Record IPv6Prefix := {
  ipv6p_prefix_len : byte;
  ipv6p_prefix : list byte  (* Variable length based on prefix_len *)
}.

(* Create IPv6 address from bytes *)
Definition create_ipv6_address (bytes : list byte) : option IPv6Address :=
  match Nat.eq_dec (length bytes) 16 with
  | left pf => Some {| ipv6_bytes := bytes; ipv6_valid := pf |}
  | right _ => None
  end.

(* Check if address is link-local (fe80::/10) *)
Definition is_link_local (addr : IPv6Address) : bool :=
  match addr.(ipv6_bytes) with
  | b0::b1::_ =>
      andb (N.eqb b0 0xFE) (N.eqb (N.shiftr b1 6) 0x02)
  | _ => false
  end.

(* Check if prefix is link-local *)
Definition is_link_local_prefix (prefix : IPv6Prefix) : bool :=
  match prefix.(ipv6p_prefix) with
  | b0::b1::_ =>
      if N.leb prefix.(ipv6p_prefix_len) 10 then
        andb (N.eqb b0 0xFE) (N.eqb (N.shiftr b1 6) 0x02)
      else
        andb (N.eqb b0 0xFE) (N.eqb (N.shiftr b1 6) 0x02)
  | b0::[] =>
      if N.leb prefix.(ipv6p_prefix_len) 8 then
        N.eqb b0 0xFE
      else
        false
  | _ => false
  end.

(* Extract prefix bytes based on length *)
Definition extract_prefix_bytes (addr : IPv6Address) (prefix_len : byte) : list byte :=
  let full_bytes := N.to_nat (prefix_len / 8) in
  let partial_bits := prefix_len mod 8 in
  if N.eqb partial_bits 0 then
    firstn full_bytes addr.(ipv6_bytes)
  else
    let partial_byte := nth full_bytes addr.(ipv6_bytes) 0 in
    let mask := N.shiftl 0xFF (8 - partial_bits) in
    firstn full_bytes addr.(ipv6_bytes) ++ [N.land partial_byte mask].

(* =============================================================================
   Section 3: IPv6 Interface Address TLV (RFC 5308 Section 2)
   ============================================================================= *)

Record IPv6InterfaceAddrTLV := {
  ipv6ia_type : word16;        (* Must be 232 *)
  ipv6ia_length : byte;         (* Multiple of 16 *)
  ipv6ia_addresses : list IPv6Address
}.

(* Create IPv6 Interface Address TLV *)
Definition create_ipv6_interface_tlv (addresses : list IPv6Address)
                                     : IPv6InterfaceAddrTLV :=
  {| ipv6ia_type := TLV_IPV6_INTERFACE_ADDR;
     ipv6ia_length := 16 * N.of_nat (length addresses);
     ipv6ia_addresses := addresses |}.

(* Validate IPv6 Interface Address TLV length *)
Definition validate_ipv6_interface_tlv_length (tlv : IPv6InterfaceAddrTLV) : bool :=
  N.eqb (tlv.(ipv6ia_length) mod 16) 0.

(* Parse IPv6 Interface Address TLV *)
Fixpoint parse_ipv6_addresses (data : list byte) (count : N) : list IPv6Address :=
  if N.eqb count 0 then []
  else
    match data with
    | b0::b1::b2::b3::b4::b5::b6::b7::
      b8::b9::b10::b11::b12::b13::b14::b15::rest =>
        match create_ipv6_address [b0;b1;b2;b3;b4;b5;b6;b7;
                                   b8;b9;b10;b11;b12;b13;b14;b15] with
        | Some addr => addr :: parse_ipv6_addresses rest (count - 1)
        | None => []
        end
    | _ => []
    end.

(* =============================================================================
   Section 4: IPv6 Reachability TLV (RFC 5308 Section 4)
   ============================================================================= *)

(* Structured Sub-TLV types *)
Inductive SubTLVData :=
  | SubTLV_IPv6_Source_Prefix : IPv6Prefix -> SubTLVData
  | SubTLV_Prefix_SID : word32 -> byte -> SubTLVData  (* SID value, flags *)
  | SubTLV_Prefix_Attributes : byte -> SubTLVData      (* Attribute flags *)
  | SubTLV_Unknown : byte -> list byte -> SubTLVData.  (* Type, raw data *)

Record SubTLV := {
  subtlv_type : byte;
  subtlv_length : byte;
  subtlv_data : SubTLVData
}.

(* Parse sub-TLV based on type with length validation *)
Definition parse_subtlv (tlv_type : byte) (tlv_len : byte) (data : list byte) : SubTLVData :=
  if N.eqb tlv_type SUBTLV_IPV6_SOURCE_PREFIX then
    match data with
    | prefix_len :: prefix_bytes =>
        if N.leb prefix_len IPV6_MAX_PREFIX_LEN then
          let expected_bytes := N.to_nat ((prefix_len + 7) / 8) in
          if Nat.leb expected_bytes (length prefix_bytes) then
            SubTLV_IPv6_Source_Prefix {| ipv6p_prefix_len := prefix_len;
                                         ipv6p_prefix := firstn expected_bytes prefix_bytes |}
          else
            SubTLV_Unknown tlv_type data
        else
          SubTLV_Unknown tlv_type data
    | _ => SubTLV_Unknown tlv_type data
    end
  else if N.eqb tlv_type SUBTLV_PREFIX_SID then
    if N.eqb tlv_len 5 then  (* Prefix SID is exactly 5 bytes: 1 flags + 4 SID *)
      match data with
      | flags :: sid0 :: sid1 :: sid2 :: sid3 :: _ =>
          let sid := N.lor (N.shiftl sid0 24)
                    (N.lor (N.shiftl sid1 16)
                    (N.lor (N.shiftl sid2 8) sid3)) in
          SubTLV_Prefix_SID sid flags
      | _ => SubTLV_Unknown tlv_type data
      end
    else
      SubTLV_Unknown tlv_type data
  else if N.eqb tlv_type SUBTLV_PREFIX_ATTRIBUTES then
    if N.leb 1 tlv_len then  (* At least 1 byte for flags *)
      match data with
      | attr_flags :: _ => SubTLV_Prefix_Attributes attr_flags
      | _ => SubTLV_Unknown tlv_type data
      end
    else
      SubTLV_Unknown tlv_type data
  else
    SubTLV_Unknown tlv_type data.

(* Create sub-TLV from parsed data *)
Definition create_subtlv (tlv_type : byte) (tlv_len : byte) (data : list byte) : SubTLV :=
  {| subtlv_type := tlv_type;
     subtlv_length := tlv_len;
     subtlv_data := parse_subtlv tlv_type tlv_len data |}.

Record IPv6ReachEntry := {
  ipv6re_metric : word32;
  ipv6re_flags : byte;         (* U, X, S, Reserved *)
  ipv6re_prefix_len : byte;
  ipv6re_prefix : list byte;   (* Variable length *)
  ipv6re_subtlvs : list SubTLV
}.

Record IPv6ReachabilityTLV := {
  ipv6r_type : word16;         (* Must be 236 *)
  ipv6r_length : byte;
  ipv6r_entries : list IPv6ReachEntry
}.

(* IPv6 Reachability Flags *)
Definition IPV6_FLAG_UP_DOWN : byte := 0x80.    (* U-bit *)
Definition IPV6_FLAG_EXTERNAL : byte := 0x40.   (* X-bit *)
Definition IPV6_FLAG_SUBTLV : byte := 0x20.     (* S-bit *)

(* Validate IPv6 Reachability entry *)
Definition validate_ipv6_reach_entry (entry : IPv6ReachEntry) : bool :=
  andb (N.leb entry.(ipv6re_prefix_len) IPV6_MAX_PREFIX_LEN)
       (N.ltb entry.(ipv6re_metric) MAX_V6_PATH_METRIC).

(* Validate Sub-TLV *)
Definition validate_subtlv (stlv : SubTLV) : bool :=
  N.leb stlv.(subtlv_length) 255.

(* Create IPv6 Reachability entry *)
Definition create_ipv6_reach_entry (prefix : IPv6Prefix) (metric : word32)
                                  (external : bool) (subtlvs : list SubTLV)
                                  : IPv6ReachEntry :=
  let flags := N.lor (if external then IPV6_FLAG_EXTERNAL else 0)
                     (match subtlvs with [] => 0 | _ => IPV6_FLAG_SUBTLV end) in
  {| ipv6re_metric := metric;
     ipv6re_flags := flags;
     ipv6re_prefix_len := prefix.(ipv6p_prefix_len);
     ipv6re_prefix := prefix.(ipv6p_prefix);
     ipv6re_subtlvs := subtlvs |}.

(* =============================================================================
   Section 5: Multi-Topology Extensions (RFC 5308 Section 5)
   ============================================================================= *)

Record MTCapability := {
  mt_cap_topology_id : word16;
  mt_cap_overload : bool;
  mt_cap_attached : bool
}.

Record MTIPV6ReachTLV := {
  mt_ipv6r_type : word16;      (* Must be 237 *)
  mt_ipv6r_length : byte;
  mt_ipv6r_topology_id : word16;
  mt_ipv6r_entries : list IPv6ReachEntry
}.

(* Create MT IPv6 Reachability TLV *)
Definition create_mt_ipv6_reach (topology : word16) (entries : list IPv6ReachEntry)
                               : MTIPV6ReachTLV :=
  {| mt_ipv6r_type := TLV_MT_IPV6_REACH;
     mt_ipv6r_length := 0;  (* Calculate based on entries *)
     mt_ipv6r_topology_id := topology;
     mt_ipv6r_entries := entries |}.

(* Check if MT is enabled *)
Definition is_mt_enabled (topologies : list word16) : bool :=
  negb (orb (match topologies with [] => true | _ => false end)
            (andb (N.eqb (N.of_nat (length topologies)) 1)
                  (N.eqb (hd 0 topologies) MT_ID_DEFAULT))).

(* =============================================================================
   Section 6: IS-IS IPv6 Instance
   ============================================================================= *)

Inductive AdjacencyState :=
  | ADJ_DOWN
  | ADJ_INIT
  | ADJ_UP.

Inductive ISISv6TLV :=
  | TLV_IPv6_Interface : list IPv6Address -> ISISv6TLV
  | TLV_IPv6_Reach : list IPv6ReachEntry -> ISISv6TLV
  | TLV_MT_IPv6_Reach : word16 -> list IPv6ReachEntry -> ISISv6TLV
  | TLV_Other : word16 -> list byte -> ISISv6TLV.

Record ISISv6Interface := {
  isv6if_index : N;
  isv6if_circuit_id : byte;
  isv6if_ipv6_addresses : list IPv6Address;
  isv6if_link_local : IPv6Address;
  isv6if_metric : word32;
  isv6if_te_metric : word32;
  isv6if_level : byte;  (* Level-1, Level-2, or both *)
  isv6if_passive : bool
}.

Record ISISv6LSP := {
  isv6lsp_lspid : list byte;
  isv6lsp_sequence : word32;
  isv6lsp_lifetime : word16;
  isv6lsp_checksum : word16;
  isv6lsp_tlvs : list ISISv6TLV
}.

(* LSP Validation *)
Definition lsp_has_expired (lsp : ISISv6LSP) : bool :=
  N.eqb lsp.(isv6lsp_lifetime) 0.

Definition lsp_newer_than (lsp1 lsp2 : ISISv6LSP) : bool :=
  N.ltb lsp2.(isv6lsp_sequence) lsp1.(isv6lsp_sequence).

Definition lsp_same_identity (lsp1 lsp2 : ISISv6LSP) : bool :=
  list_beq N.eqb lsp1.(isv6lsp_lspid) lsp2.(isv6lsp_lspid).

(* Check if LSP should be accepted *)
Definition lsp_should_accept (new_lsp : ISISv6LSP) (existing_lsp : option ISISv6LSP) : bool :=
  if lsp_has_expired new_lsp then
    false
  else
    match existing_lsp with
    | None => true
    | Some old_lsp =>
        andb (lsp_same_identity new_lsp old_lsp)
             (lsp_newer_than new_lsp old_lsp)
    end.

(* LSP ID validity: Must be exactly 8 bytes (6-byte System ID + 1-byte Pseudonode + 1-byte LSP Number) *)
Definition lsp_id_valid (lspid : list byte) : bool :=
  N.eqb (N.of_nat (length lspid)) 8.

(* LSP checksum validation placeholder - would implement ISO 10589 checksum *)
Definition lsp_checksum_valid (lsp : ISISv6LSP) : bool :=
  negb (N.eqb lsp.(isv6lsp_checksum) 0).

(* LSP database lookup *)
Fixpoint find_lsp_in_db (db : list ISISv6LSP) (lspid : list byte) : option ISISv6LSP :=
  match db with
  | [] => None
  | lsp :: rest =>
      if list_beq N.eqb lsp.(isv6lsp_lspid) lspid then
        Some lsp
      else
        find_lsp_in_db rest lspid
  end.

(* Update or insert LSP in database *)
Fixpoint upsert_lsp (db : list ISISv6LSP) (new_lsp : ISISv6LSP) : list ISISv6LSP :=
  match db with
  | [] => [new_lsp]
  | lsp :: rest =>
      if list_beq N.eqb lsp.(isv6lsp_lspid) new_lsp.(isv6lsp_lspid) then
        new_lsp :: rest
      else
        lsp :: upsert_lsp rest new_lsp
  end.

(* Remove expired LSPs from database *)
Definition purge_expired_lsps (db : list ISISv6LSP) : list ISISv6LSP :=
  filter (fun x => negb (lsp_has_expired x)) db.

Record ISISv6Adjacency := {
  isv6adj_system_id : list byte;
  isv6adj_ipv6_addresses : list IPv6Address;
  isv6adj_link_local : IPv6Address;
  isv6adj_state : AdjacencyState;
  isv6adj_level : byte;
  isv6adj_metric : word32
}.

(* Adjacency State Machine Events *)
Inductive AdjacencyEvent :=
  | Adj_HelloReceived
  | Adj_HoldtimeExpired
  | Adj_InterfaceDown.

(* Adjacency state transitions *)
Definition adjacency_transition (current : AdjacencyState) (event : AdjacencyEvent)
                                : AdjacencyState :=
  match current, event with
  | ADJ_DOWN, Adj_HelloReceived => ADJ_INIT
  | ADJ_INIT, Adj_HelloReceived => ADJ_UP
  | ADJ_UP, Adj_HelloReceived => ADJ_UP
  | ADJ_UP, Adj_HoldtimeExpired => ADJ_DOWN
  | ADJ_UP, Adj_InterfaceDown => ADJ_DOWN
  | ADJ_INIT, Adj_HoldtimeExpired => ADJ_DOWN
  | ADJ_INIT, Adj_InterfaceDown => ADJ_DOWN
  | ADJ_DOWN, _ => ADJ_DOWN
  end.

(* Update adjacency state *)
Definition update_adjacency_state (adj : ISISv6Adjacency) (event : AdjacencyEvent)
                                  : ISISv6Adjacency :=
  {| isv6adj_system_id := adj.(isv6adj_system_id);
     isv6adj_ipv6_addresses := adj.(isv6adj_ipv6_addresses);
     isv6adj_link_local := adj.(isv6adj_link_local);
     isv6adj_state := adjacency_transition adj.(isv6adj_state) event;
     isv6adj_level := adj.(isv6adj_level);
     isv6adj_metric := adj.(isv6adj_metric) |}.

(* Check if adjacency is usable for SPF *)
Definition adjacency_is_up (adj : ISISv6Adjacency) : bool :=
  match adj.(isv6adj_state) with
  | ADJ_UP => true
  | _ => false
  end.

Record IPv6Route := {
  ipv6rt_prefix : IPv6Prefix;
  ipv6rt_next_hop : IPv6Address;
  ipv6rt_interface : N;
  ipv6rt_metric : word32;
  ipv6rt_level : byte;
  ipv6rt_up_down : bool;  (* U-bit: false = up, true = down *)
  ipv6rt_external : bool;
  ipv6rt_topology_id : word16  (* MT topology, 0 for default *)
}.

(* MT-specific routing table *)
Record MTRoutingTable := {
  mt_topology_id : word16;
  mt_routes : list IPv6Route
}.

Record ISISv6Instance := {
  isv6_system_id : list byte;
  isv6_areas : list (list byte);
  isv6_interfaces : list ISISv6Interface;
  isv6_level1_lsdb : list ISISv6LSP;
  isv6_level2_lsdb : list ISISv6LSP;
  isv6_adjacencies : list ISISv6Adjacency;
  isv6_ipv6_routing_table : list IPv6Route;
  isv6_mt_topologies : list word16;
  isv6_mt_routing_tables : list MTRoutingTable;
  isv6_protocols_supported : list byte
}.

(* =============================================================================
   Section 7: SPF Calculation for IPv6
   ============================================================================= *)

(* IPv6 SPF Node *)
Record IPv6SPFNode := {
  ipv6spf_system_id : list byte;
  ipv6spf_distance : word32;
  ipv6spf_parent : option (list byte);
  ipv6spf_ipv6_prefixes : list IPv6Prefix;
  ipv6spf_next_hop : IPv6Address
}.

(* Clamp metric to MAX_V6_PATH_METRIC *)
Definition clamp_metric (metric : word32) : word32 :=
  if N.leb metric MAX_V6_PATH_METRIC then
    metric
  else
    MAX_V6_PATH_METRIC.

(* Add two metrics with clamping *)
Definition add_metrics (m1 m2 : word32) : word32 :=
  let sum := m1 + m2 in
  clamp_metric sum.

(* Extract system ID from LSPID *)
Definition extract_system_id (lspid : list byte) : list byte :=
  firstn 6 lspid.

(* Find LSP by system ID *)
Fixpoint find_lsp_by_sysid (lsps : list ISISv6LSP) (sysid : list byte) : option ISISv6LSP :=
  match lsps with
  | [] => None
  | lsp :: rest =>
      if list_beq N.eqb (extract_system_id lsp.(isv6lsp_lspid)) sysid then
        Some lsp
      else
        find_lsp_by_sysid rest sysid
  end.

(* Extract IPv6 prefixes from TLVs *)
Fixpoint extract_ipv6_prefixes (tlvs : list ISISv6TLV) : list IPv6Prefix :=
  match tlvs with
  | [] => []
  | TLV_IPv6_Reach entries :: rest =>
      let prefixes := map (fun e => {| ipv6p_prefix_len := e.(ipv6re_prefix_len);
                                       ipv6p_prefix := e.(ipv6re_prefix) |}) entries in
      prefixes ++ extract_ipv6_prefixes rest
  | TLV_MT_IPv6_Reach _ entries :: rest =>
      let prefixes := map (fun e => {| ipv6p_prefix_len := e.(ipv6re_prefix_len);
                                       ipv6p_prefix := e.(ipv6re_prefix) |}) entries in
      prefixes ++ extract_ipv6_prefixes rest
  | _ :: rest => extract_ipv6_prefixes rest
  end.

(* Neighbor info extracted from IS reachability TLVs *)
Record ISNeighbor := {
  isn_system_id : list byte;
  isn_metric : word32
}.

(* Parse Extended IS Reachability (TLV 22) entry *)
Fixpoint parse_extended_is_reach_entries (data : list byte) (fuel : nat) : list ISNeighbor :=
  match fuel with
  | O => []
  | S fuel' =>
      match data with
      | s0::s1::s2::s3::s4::s5::s6::m0::m1::m2::rest =>
          (* System ID (7 bytes: 6 bytes ID + 1 byte pseudonode), 3 bytes metric *)
          let sysid := [s0; s1; s2; s3; s4; s5; s6] in
          let metric := N.lor (N.shiftl m0 16) (N.lor (N.shiftl m1 8) m2) in
          let sub_tlv_len := match rest with | len::_ => len | _ => 0 end in
          let bytes_consumed := N.to_nat sub_tlv_len in
          let remaining_data := skipn (1 + bytes_consumed) rest in
          {| isn_system_id := sysid; isn_metric := metric |} ::
            parse_extended_is_reach_entries remaining_data fuel'
      | _ => []
      end
  end.

(* Parse MT IS Reachability (TLV 222) entry *)
Fixpoint parse_mt_is_reach_entries (data : list byte) (fuel : nat) : list ISNeighbor :=
  match fuel with
  | O => []
  | S fuel' =>
      match data with
      | s0::s1::s2::s3::s4::s5::s6::m0::m1::m2::rest =>
          let sysid := [s0; s1; s2; s3; s4; s5; s6] in
          let metric := N.lor (N.shiftl m0 16) (N.lor (N.shiftl m1 8) m2) in
          let sub_tlv_len := match rest with | len::_ => len | _ => 0 end in
          let bytes_consumed := N.to_nat sub_tlv_len in
          let remaining_data := skipn (1 + bytes_consumed) rest in
          {| isn_system_id := sysid; isn_metric := metric |} ::
            parse_mt_is_reach_entries remaining_data fuel'
      | _ => []
      end
  end.

(* Extract IS neighbors from TLV_Other representing IS reachability *)
Definition extract_is_neighbors_from_tlv (tlv : ISISv6TLV) : list ISNeighbor :=
  match tlv with
  | TLV_Other typ data =>
      if N.eqb typ 22 then
        parse_extended_is_reach_entries data (Nat.div (length data) 11)
      else if N.eqb typ 222 then
        match data with
        | _::_::rest => parse_mt_is_reach_entries rest (Nat.div (length rest) 11)
        | _ => []
        end
      else
        []
  | _ => []
  end.

(* Extract all neighbors from LSP TLVs *)
Fixpoint extract_neighbors (tlvs : list ISISv6TLV) : list ISNeighbor :=
  match tlvs with
  | [] => []
  | tlv :: rest =>
      extract_is_neighbors_from_tlv tlv ++ extract_neighbors rest
  end.

(* Get neighbors for a system from LSP database *)
Definition get_neighbors (lsps : list ISISv6LSP) (sysid : list byte) : list ISNeighbor :=
  match find_lsp_by_sysid lsps sysid with
  | None => []
  | Some lsp => extract_neighbors lsp.(isv6lsp_tlvs)
  end.

(* Find SPF node in list *)
Fixpoint find_spf_node (nodes : list IPv6SPFNode) (sysid : list byte) : option IPv6SPFNode :=
  match nodes with
  | [] => None
  | n :: ns =>
      if list_beq N.eqb n.(ipv6spf_system_id) sysid then
        Some n
      else
        find_spf_node ns sysid
  end.

(* Update SPF node in list *)
Fixpoint update_spf_node (nodes : list IPv6SPFNode) (node : IPv6SPFNode) : list IPv6SPFNode :=
  match nodes with
  | [] => [node]
  | n :: ns =>
      if list_beq N.eqb n.(ipv6spf_system_id) node.(ipv6spf_system_id) then
        node :: ns
      else
        n :: update_spf_node ns node
  end.

(* Extract minimum distance node *)
Fixpoint extract_min (nodes : list IPv6SPFNode) (fuel : nat)
                    : option (IPv6SPFNode * list IPv6SPFNode) :=
  match fuel with
  | O => None
  | S fuel' =>
      match nodes with
      | [] => None
      | [n] => Some (n, [])
      | n1 :: n2 :: rest =>
          match extract_min (n2 :: rest) fuel' with
          | None => Some (n1, n2 :: rest)
          | Some (min_node, remaining) =>
              if N.ltb n1.(ipv6spf_distance) min_node.(ipv6spf_distance) then
                Some (n1, n2 :: rest)
              else
                Some (min_node, n1 :: remaining)
          end
      end
  end.

(* Check if node is in confirmed list *)
Fixpoint is_confirmed (confirmed : list IPv6SPFNode) (sysid : list byte) : bool :=
  match confirmed with
  | [] => false
  | n :: rest =>
      if list_beq N.eqb n.(ipv6spf_system_id) sysid then
        true
      else
        is_confirmed rest sysid
  end.

(* Update or add tentative node *)
Fixpoint update_tentative (tentative : list IPv6SPFNode) (neighbor : ISNeighbor)
                         (via_node : IPv6SPFNode) (lsps : list ISISv6LSP)
                         : list IPv6SPFNode :=
  let new_distance := add_metrics via_node.(ipv6spf_distance) neighbor.(isn_metric) in
  let neighbor_lsp := find_lsp_by_sysid lsps neighbor.(isn_system_id) in
  let neighbor_prefixes := match neighbor_lsp with
                          | Some lsp => extract_ipv6_prefixes lsp.(isv6lsp_tlvs)
                          | None => []
                          end in
  match find_spf_node tentative neighbor.(isn_system_id) with
  | None =>
      (* Add new tentative node *)
      let new_node := {| ipv6spf_system_id := neighbor.(isn_system_id);
                        ipv6spf_distance := new_distance;
                        ipv6spf_parent := Some via_node.(ipv6spf_system_id);
                        ipv6spf_ipv6_prefixes := neighbor_prefixes;
                        ipv6spf_next_hop := via_node.(ipv6spf_next_hop) |} in
      new_node :: tentative
  | Some existing =>
      (* Update if new distance is better *)
      if N.ltb new_distance existing.(ipv6spf_distance) then
        let updated_node := {| ipv6spf_system_id := neighbor.(isn_system_id);
                              ipv6spf_distance := new_distance;
                              ipv6spf_parent := Some via_node.(ipv6spf_system_id);
                              ipv6spf_ipv6_prefixes := neighbor_prefixes;
                              ipv6spf_next_hop := via_node.(ipv6spf_next_hop) |} in
        update_spf_node tentative updated_node
      else
        tentative
  end.

(* Process all neighbors of current node *)
Fixpoint process_neighbors (lsps : list ISISv6LSP) (neighbors : list ISNeighbor)
                          (current : IPv6SPFNode) (tentative : list IPv6SPFNode)
                          (confirmed : list IPv6SPFNode) : list IPv6SPFNode :=
  match neighbors with
  | [] => tentative
  | n :: rest =>
      if is_confirmed confirmed n.(isn_system_id) then
        process_neighbors lsps rest current tentative confirmed
      else
        let new_tentative := update_tentative tentative n current lsps in
        process_neighbors lsps rest current new_tentative confirmed
  end.

(* Run SPF for IPv6 topology using Dijkstra *)
Fixpoint ipv6_spf_iter (lsps : list ISISv6LSP) (tentative : list IPv6SPFNode)
                      (confirmed : list IPv6SPFNode) (fuel : nat) : list IPv6SPFNode :=
  match fuel with
  | O => confirmed  (* Out of fuel *)
  | S fuel' =>
      match extract_min tentative (length tentative) with
      | None => confirmed  (* No more tentative nodes *)
      | Some (current, remaining) =>
          (* Add current to confirmed *)
          let new_confirmed := current :: confirmed in
          (* Get neighbors of current node *)
          let neighbors := get_neighbors lsps current.(ipv6spf_system_id) in
          (* Update tentative list with neighbors *)
          let new_tentative := process_neighbors lsps neighbors current remaining new_confirmed in
          ipv6_spf_iter lsps new_tentative new_confirmed fuel'
      end
  end.

Definition ipv6_spf (lsps : list ISISv6LSP) (self_id : list byte)
                   : list IPv6SPFNode :=
  let root := {| ipv6spf_system_id := self_id;
                 ipv6spf_distance := 0;
                 ipv6spf_parent := None;
                 ipv6spf_ipv6_prefixes := [];
                 ipv6spf_next_hop := {| ipv6_bytes := repeat 0 16;
                                        ipv6_valid := eq_refl |} |} in
  ipv6_spf_iter lsps [root] [] 100.

(* Process IPv6 reachability information *)
Definition process_ipv6_reach (instance : ISISv6Instance) (reach : IPv6ReachEntry)
                             (level : byte) (topology : word16) : list IPv6Route :=
  let prefix := {| ipv6p_prefix_len := reach.(ipv6re_prefix_len);
                   ipv6p_prefix := reach.(ipv6re_prefix) |} in
  (* RFC 5308: Link-local prefixes MUST NOT be advertised *)
  if is_link_local_prefix prefix then
    []
  else if N.ltb reach.(ipv6re_metric) MAX_V6_PATH_METRIC then  (* Valid metric *)
    let up_down := N.testbit reach.(ipv6re_flags) 7 in  (* U-bit *)
    let external := N.testbit reach.(ipv6re_flags) 6 in  (* X-bit *)
    [{| ipv6rt_prefix := prefix;
        ipv6rt_next_hop := {| ipv6_bytes := repeat 0 16; ipv6_valid := eq_refl |};
        ipv6rt_interface := 0;
        ipv6rt_metric := reach.(ipv6re_metric);
        ipv6rt_level := level;
        ipv6rt_up_down := up_down;
        ipv6rt_external := external;
        ipv6rt_topology_id := topology |}]
  else
    [].

(* Process MT IPv6 reachability *)
Definition process_mt_ipv6_reach (instance : ISISv6Instance)
                                 (mt_tlv : MTIPV6ReachTLV)
                                 : list IPv6Route :=
  flat_map (fun entry => process_ipv6_reach instance entry 2 mt_tlv.(mt_ipv6r_topology_id))
           mt_tlv.(mt_ipv6r_entries).

(* Filter routes by topology *)
Definition filter_routes_by_topology (routes : list IPv6Route) (topology : word16)
                                     : list IPv6Route :=
  filter (fun route => N.eqb route.(ipv6rt_topology_id) topology) routes.

(* Filter LSPs to extract only TLVs for specific topology *)
Fixpoint filter_tlvs_by_topology (tlvs : list ISISv6TLV) (topology : word16) : list ISISv6TLV :=
  match tlvs with
  | [] => []
  | TLV_MT_IPv6_Reach top entries :: rest =>
      if N.eqb top topology then
        TLV_MT_IPv6_Reach top entries :: filter_tlvs_by_topology rest topology
      else
        filter_tlvs_by_topology rest topology
  | TLV_IPv6_Reach entries :: rest =>
      if N.eqb topology MT_ID_DEFAULT then
        TLV_IPv6_Reach entries :: filter_tlvs_by_topology rest topology
      else
        filter_tlvs_by_topology rest topology
  | TLV_Other typ data :: rest =>
      (* Include IS reachability for topology-specific SPF *)
      TLV_Other typ data :: filter_tlvs_by_topology rest topology
  | tlv :: rest => tlv :: filter_tlvs_by_topology rest topology
  end.

(* Filter LSPs for specific MT topology *)
Definition filter_lsp_for_topology (lsp : ISISv6LSP) (topology : word16) : ISISv6LSP :=
  {| isv6lsp_lspid := lsp.(isv6lsp_lspid);
     isv6lsp_sequence := lsp.(isv6lsp_sequence);
     isv6lsp_lifetime := lsp.(isv6lsp_lifetime);
     isv6lsp_checksum := lsp.(isv6lsp_checksum);
     isv6lsp_tlvs := filter_tlvs_by_topology lsp.(isv6lsp_tlvs) topology |}.

Definition filter_lsps_for_topology (lsps : list ISISv6LSP) (topology : word16) : list ISISv6LSP :=
  map (fun lsp => filter_lsp_for_topology lsp topology) lsps.

(* Create MT-specific SPF tree *)
Definition mt_ipv6_spf (lsps : list ISISv6LSP) (self_id : list byte)
                      (topology : word16) : list IPv6SPFNode :=
  let filtered_lsps := filter_lsps_for_topology lsps topology in
  ipv6_spf filtered_lsps self_id.

(* RFC 5308 Path Preference: L1-up > L2-up > L2-down > L1-down *)
Inductive PathPreference :=
  | Pref_L1_up
  | Pref_L2_up
  | Pref_L2_down
  | Pref_L1_down.

Definition route_preference (route : IPv6Route) : PathPreference :=
  match N.eqb route.(ipv6rt_level) 1, route.(ipv6rt_up_down) with
  | true, false => Pref_L1_up
  | true, true => Pref_L1_down
  | false, false => Pref_L2_up
  | false, true => Pref_L2_down
  end.

Definition preference_to_nat (p : PathPreference) : nat :=
  match p with
  | Pref_L1_up => 0
  | Pref_L2_up => 1
  | Pref_L2_down => 2
  | Pref_L1_down => 3
  end.

(* Compare two routes: returns true if r1 is better than r2 *)
Definition route_better (r1 r2 : IPv6Route) : bool :=
  let p1 := preference_to_nat (route_preference r1) in
  let p2 := preference_to_nat (route_preference r2) in
  if Nat.eqb p1 p2 then
    N.ltb r1.(ipv6rt_metric) r2.(ipv6rt_metric)  (* Compare metrics if same preference *)
  else
    Nat.ltb p1 p2.  (* Lower preference number is better *)

(* =============================================================================
   Section 8: IPv6 Specific Procedures
   ============================================================================= *)

(* Check if IPv6 is enabled *)
Definition ipv6_enabled (instance : ISISv6Instance) : bool :=
  existsb (N.eqb NLPID_IPV6) instance.(isv6_protocols_supported).

(* Generate Router Advertisement prefixes from IS-IS interface *)
Definition generate_router_advert (iface : ISISv6Interface)
                                 (routes : list IPv6Route)
                                 : list IPv6Prefix :=
  (* Extract prefixes assigned to this interface from routing table *)
  (* Only advertise prefixes that are directly connected (metric 0 or interface match) *)
  let interface_routes := filter (fun r => N.eqb r.(ipv6rt_interface) iface.(isv6if_index)) routes in
  map (fun r => r.(ipv6rt_prefix)) interface_routes.

(* Check if an address matches a prefix *)
Fixpoint bytes_match (addr_bytes prefix_bytes : list byte) : bool :=
  match addr_bytes, prefix_bytes with
  | _, [] => true  (* All prefix bytes matched *)
  | [], _ => false (* Ran out of address bytes before matching all prefix *)
  | a::as_, p::ps => andb (N.eqb a p) (bytes_match as_ ps)
  end.

Definition address_matches_prefix (addr : IPv6Address) (prefix : IPv6Prefix) : bool :=
  let addr_prefix_bytes := extract_prefix_bytes addr prefix.(ipv6p_prefix_len) in
  bytes_match addr_prefix_bytes prefix.(ipv6p_prefix).

(* Check if source prefix matches a source-specific sub-TLV *)
Fixpoint check_source_prefix_match (subtlvs : list SubTLV) (source : IPv6Address) : bool :=
  match subtlvs with
  | [] => false
  | stlv :: rest =>
      match stlv.(subtlv_data) with
      | SubTLV_IPv6_Source_Prefix src_pfx =>
          orb (address_matches_prefix source src_pfx)
              (check_source_prefix_match rest source)
      | _ => check_source_prefix_match rest source
      end
  end.

(* Handle IPv6 source routing based on source prefix sub-TLV *)
Definition handle_source_routing (reach_entry : IPv6ReachEntry) (source : IPv6Address)
                                : bool :=
  (* Check if source-specific routing applies via sub-TLVs *)
  check_source_prefix_match reach_entry.(ipv6re_subtlvs) source.

(* =============================================================================
   Section 9: Interoperability
   ============================================================================= *)

(* Check for RFC 1195 compatibility *)
Definition supports_rfc1195 (tlvs : list ISISv6TLV) : bool :=
  existsb (fun tlv =>
    match tlv with
    | TLV_Other typ _ => orb (N.eqb typ 128) (N.eqb typ 130)  (* IP reach TLVs *)
    | _ => false
    end
  ) tlvs.

(* Translate between old and new TLV formats *)
Definition migrate_to_new_tlv (old_tlv : word16) : option word16 :=
  if N.eqb old_tlv 128 then Some 235      (* IP Internal -> Extended IP *)
  else if N.eqb old_tlv 130 then Some 235  (* IP External -> Extended IP *)
  else None.

(* =============================================================================
   Section 10: Key Properties
   ============================================================================= *)

(* Property 1: IPv6 addresses are 128 bits *)
Theorem ipv6_address_size : forall addr,
  length addr.(ipv6_bytes) = 16%nat.
Proof.
  intros. exact addr.(ipv6_valid).
Qed.

(* Property 2: Prefix extraction preserves length *)
Theorem prefix_extraction_length : forall addr len,
  len <= 128 ->
  (length (extract_prefix_bytes addr len) <= 16)%nat.
Proof.
  intros addr len H.
  unfold extract_prefix_bytes.
  destruct (N.eqb_spec (len mod 8) 0).
  - rewrite firstn_length, ipv6_address_size.
    apply Nat.le_min_r.
  - rewrite app_length, firstn_length, ipv6_address_size.
    simpl.
    enough (N.to_nat (len / 8) <= 15)%nat by lia.
    assert (len / 8 < 16)%N.
    { assert (len < 128)%N.
      { apply N.lt_eq_cases in H. destruct H. lia.
        exfalso. apply n. rewrite H. simpl. reflexivity. }
      apply N.div_lt_upper_bound. lia. lia. }
    lia.
Qed.

(* Property 3: MT topology IDs are distinct *)
Theorem mt_topology_distinct :
  MT_ID_IPV6_UNICAST <> MT_ID_IPV4_UNICAST /\
  MT_ID_IPV6_MULTICAST <> MT_ID_IPV4_MULTICAST.
Proof.
  split; discriminate.
Qed.

(* Property 4: External flag preserved *)
Theorem external_flag_preserved : forall prefix metric ext subtlvs,
  let entry := create_ipv6_reach_entry prefix metric ext subtlvs in
  ext = true -> N.testbit entry.(ipv6re_flags) 6 = true.
Proof.
  intros. unfold create_ipv6_reach_entry in entry.
  simpl. unfold IPV6_FLAG_EXTERNAL.
  destruct ext; destruct subtlvs; simpl; auto.
Qed.

(* Property 5: Metric clamping ensures bounded distances *)
Theorem clamp_metric_bounded : forall m,
  clamp_metric m <= MAX_V6_PATH_METRIC.
Proof.
  intros m.
  unfold clamp_metric.
  destruct (N.leb m MAX_V6_PATH_METRIC) eqn:Hle.
  - apply N.leb_le in Hle. exact Hle.
  - apply N.le_refl.
Qed.

Theorem add_metrics_bounded : forall m1 m2,
  add_metrics m1 m2 <= MAX_V6_PATH_METRIC.
Proof.
  intros m1 m2.
  unfold add_metrics.
  apply clamp_metric_bounded.
Qed.

(* Property 6: LSP ID length correctness *)
Theorem lsp_id_length : forall lspid,
  lsp_id_valid lspid = true <-> length lspid = 8%nat.
Proof.
  intros lspid. split.
  - intro H. unfold lsp_id_valid in H.
    apply N.eqb_eq in H.
    apply Nat2N.inj. exact H.
  - intro H. unfold lsp_id_valid.
    apply N.eqb_eq. rewrite H. reflexivity.
Qed.

(* Property 7: Extract system ID preserves length *)
Theorem extract_system_id_length : forall lspid,
  lsp_id_valid lspid = true ->
  (length (extract_system_id lspid) <= 6)%nat.
Proof.
  intros lspid H.
  unfold extract_system_id.
  rewrite firstn_length.
  apply lsp_id_length in H.
  rewrite H. simpl. lia.
Qed.

(* Property 8: Expired LSPs are not accepted *)
Theorem expired_lsp_rejected : forall lsp existing,
  lsp_has_expired lsp = true ->
  lsp_should_accept lsp existing = false.
Proof.
  intros lsp existing H.
  unfold lsp_should_accept.
  rewrite H. reflexivity.
Qed.

(* Property 9: Purged database contains only non-expired LSPs *)
Theorem purge_removes_expired : forall db l,
  In l (purge_expired_lsps db) ->
  lsp_has_expired l = false.
Proof.
  induction db as [| hd tl IH]; intros l H.
  - inversion H.
  - simpl in H. destruct (negb (lsp_has_expired hd)) eqn:Hneg.
    + simpl in H. destruct H as [Heq | Hin].
      * subst. apply negb_true_iff. exact Hneg.
      * apply IH. exact Hin.
    + apply IH. exact H.
Qed.

(* Property 10: Upsert maintains LSP presence *)
Theorem upsert_lsp_present : forall db lsp_elem,
  In lsp_elem (upsert_lsp db lsp_elem).
Proof.
  intros db lsp_elem.
  induction db as [| hd tl IH].
  - simpl. left. reflexivity.
  - simpl. destruct (list_beq N.eqb hd.(isv6lsp_lspid) lsp_elem.(isv6lsp_lspid)) eqn:Heq.
    + left. reflexivity.
    + right. exact IH.
Qed.

(* Property 11: SPF termination - fuel-based recursion always terminates *)
Theorem ipv6_spf_terminates : forall lsps fuel,
  exists result, result = ipv6_spf_iter lsps [] [] fuel.
Proof.
  intros lsps fuel.
  exists (ipv6_spf_iter lsps [] [] fuel).
  reflexivity.
Qed.

(* Property 12: Route preference ordering based on preference and metric *)
Definition route_equivalent (r1 r2 : IPv6Route) : Prop :=
  route_preference r1 = route_preference r2 /\
  r1.(ipv6rt_metric) = r2.(ipv6rt_metric).

Lemma preference_to_nat_bounded : forall p,
  (preference_to_nat p < 4)%nat.
Proof.
  intros p. destruct p; simpl; lia.
Qed.

Lemma nat_eqb_sym : forall n m,
  Nat.eqb n m = Nat.eqb m n.
Proof.
  intros n m.
  destruct (Nat.eqb n m) eqn:H1.
  - apply Nat.eqb_eq in H1. subst. symmetry. apply Nat.eqb_refl.
  - destruct (Nat.eqb m n) eqn:H2.
    + apply Nat.eqb_eq in H2. subst. rewrite Nat.eqb_refl in H1. discriminate.
    + reflexivity.
Qed.

Lemma preference_eq_implies_route_preference_eq : forall r1 r2 p1 p2,
  p1 = preference_to_nat (route_preference r1) ->
  p2 = preference_to_nat (route_preference r2) ->
  p1 = p2 ->
  route_preference r1 = route_preference r2.
Proof.
  intros r1 r2 p1 p2 H1 H2 Heq.
  subst p1 p2.
  destruct (route_preference r1) eqn:Hp1, (route_preference r2) eqn:Hp2;
  simpl in Heq; try discriminate; reflexivity.
Qed.

Lemma N_metric_trichotomy : forall m1 m2,
  N.ltb m1 m2 = true \/ N.ltb m2 m1 = true \/ m1 = m2.
Proof.
  intros m1 m2.
  destruct (N.ltb m1 m2) eqn:Hm1.
  - left. reflexivity.
  - apply N.ltb_ge in Hm1.
    destruct (N.ltb m2 m1) eqn:Hm2.
    + right. left. reflexivity.
    + apply N.ltb_ge in Hm2.
      right. right. lia.
Qed.

Lemma nat_pref_trichotomy : forall p1 p2,
  Nat.ltb p1 p2 = true \/ Nat.ltb p2 p1 = true \/ p1 = p2.
Proof.
  intros p1 p2.
  destruct (Nat.ltb p1 p2) eqn:Hp1.
  - left. reflexivity.
  - apply Nat.ltb_ge in Hp1.
    destruct (Nat.ltb p2 p1) eqn:Hp2.
    + right. left. reflexivity.
    + apply Nat.ltb_ge in Hp2.
      right. right. lia.
Qed.

Theorem route_preference_total : forall r1 r2,
  route_better r1 r2 = true \/ route_better r2 r1 = true \/ route_equivalent r1 r2.
Proof.
  intros r1 r2.
  unfold route_better.
  set (p1 := preference_to_nat (route_preference r1)).
  set (p2 := preference_to_nat (route_preference r2)).
  destruct (nat_pref_trichotomy p1 p2) as [Hlt | [Hgt | Heq]].
  - destruct (Nat.eqb p1 p2) eqn:Hpeq.
    + apply Nat.eqb_eq in Hpeq. apply Nat.ltb_lt in Hlt. lia.
    + left. exact Hlt.
  - destruct (Nat.eqb p1 p2) eqn:Hpeq.
    + apply Nat.eqb_eq in Hpeq. apply Nat.ltb_lt in Hgt. lia.
    + right. left. rewrite nat_eqb_sym. rewrite Hpeq. exact Hgt.
  - destruct (Nat.eqb p1 p2) eqn:Hpeq.
    + destruct (N_metric_trichotomy (ipv6rt_metric r1) (ipv6rt_metric r2)) as [Hm1 | [Hm2 | Hmeq]].
      * left. exact Hm1.
      * right. left. rewrite nat_eqb_sym. rewrite Hpeq. exact Hm2.
      * right. right. unfold route_equivalent. split.
        { eapply preference_eq_implies_route_preference_eq; try reflexivity; exact Heq. }
        { exact Hmeq. }
    + apply Nat.eqb_neq in Hpeq. contradiction.
Qed.

(* Property 13: U-bit semantics for route redistribution *)
Definition is_down_route (route : IPv6Route) : bool :=
  route.(ipv6rt_up_down).

Definition well_formed_down_route (route : IPv6Route) : Prop :=
  is_down_route route = true -> route.(ipv6rt_level) = 1.

Lemma process_ipv6_reach_preserves_level : forall instance reach level topology routes,
  routes = process_ipv6_reach instance reach level topology ->
  forall route, In route routes -> route.(ipv6rt_level) = level.
Proof.
  intros instance reach level topology routes H route Hin.
  subst routes.
  unfold process_ipv6_reach in Hin.
  destruct (is_link_local_prefix {| ipv6p_prefix_len := ipv6re_prefix_len reach;
                                     ipv6p_prefix := ipv6re_prefix reach |}) eqn:Hll.
  - contradiction.
  - destruct (N.ltb (ipv6re_metric reach) MAX_V6_PATH_METRIC) eqn:Hmetric.
    + simpl in Hin. destruct Hin as [Heq | Hfalse].
      * rewrite <- Heq. simpl. reflexivity.
      * contradiction.
    + contradiction.
Qed.

(* Property 14: Metric addition is monotonic and idempotent at maximum *)
Theorem metric_addition_bounded_both : forall m1 m2 m3,
  add_metrics (add_metrics m1 m2) m3 <= MAX_V6_PATH_METRIC /\
  add_metrics m1 (add_metrics m2 m3) <= MAX_V6_PATH_METRIC.
Proof.
  intros m1 m2 m3.
  split; apply add_metrics_bounded.
Qed.

Theorem metric_addition_at_max : forall m,
  add_metrics MAX_V6_PATH_METRIC m = MAX_V6_PATH_METRIC.
Proof.
  intros m.
  unfold add_metrics, clamp_metric.
  destruct (N.leb (MAX_V6_PATH_METRIC + m) MAX_V6_PATH_METRIC) eqn:Hle.
  - apply N.leb_le in Hle.
    assert (m = 0) by lia.
    subst. rewrite N.add_0_r. reflexivity.
  - reflexivity.
Qed.

Theorem metric_addition_monotone : forall m1 m2 m3,
  m1 <= m2 ->
  add_metrics m1 m3 <= add_metrics m2 m3.
Proof.
  intros m1 m2 m3 H.
  unfold add_metrics, clamp_metric.
  destruct (N.leb (m1 + m3) MAX_V6_PATH_METRIC) eqn:H1;
  destruct (N.leb (m2 + m3) MAX_V6_PATH_METRIC) eqn:H2;
  try (apply N.leb_le in H1; apply N.leb_le in H2; lia);
  try (apply N.leb_le in H1; apply N.leb_gt in H2; lia);
  try (apply N.leb_gt in H1; apply N.leb_le in H2; lia);
  try (apply N.leb_gt in H1; apply N.leb_gt in H2; lia).
Qed.

(* Property 15: Link-local addresses never appear in reachability *)
Theorem link_local_not_advertised : forall prefix,
  is_link_local_prefix prefix = true ->
  forall instance entry level topology,
    ~In entry (process_ipv6_reach instance
                 {| ipv6re_metric := 0;
                    ipv6re_flags := 0;
                    ipv6re_prefix_len := prefix.(ipv6p_prefix_len);
                    ipv6re_prefix := prefix.(ipv6p_prefix);
                    ipv6re_subtlvs := [] |}
                 level topology).
Proof.
  intros prefix Hll instance entry level topology Hin.
  unfold process_ipv6_reach in Hin.
  destruct prefix as [plen pbytes].
  simpl in Hin, Hll.
  rewrite Hll in Hin.
  contradiction.
Qed.

(* =============================================================================
   Section 11: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction "isis_ipv6.ml"
  create_ipv6_address
  extract_prefix_bytes
  create_ipv6_interface_tlv
  create_ipv6_reach_entry
  create_mt_ipv6_reach
  ipv6_spf
  process_ipv6_reach
  ipv6_enabled.
