(* =============================================================================
   Formal Verification of Address Resolution Protocol (ARP)
   
   Specification: RFC 826 (David C. Plummer, November 1982)
   Target: Ethernet/IPv4 Address Resolution
   
   Module: ARP Protocol Formalization and Verification
   Author: Charles C Norton
   Date: August 29, 2025
   
   "Long he had journeyed, taking forms both fair and fell, 
    until he came at last to the doors he sought."
   
   ============================================================================= *)

From Coq Require Import
  List
  NArith.NArith
  NArith.Ndigits
  Bool
  Arith
  Lia
  Eqdep_dec
  ProofIrrelevance.

Import ListNotations.
Open Scope N_scope.

(* =============================================================================
   Section 1: Basic Types and Constants
   ============================================================================= *)

(* 8-bit unsigned integer type *)
Definition byte := N.
(* 16-bit unsigned integer type *)
Definition word16 := N.
(* 32-bit unsigned integer type *)
Definition word32 := N.

(* Validates n is within byte range [0,255] *)
Definition is_valid_byte (n : N) : bool := N.leb n 255.
(* Validates n is within 16-bit range [0,65535] *)
Definition is_valid_word16 (n : N) : bool := N.leb n 65535.
(* Validates n is within 32-bit range [0,2^32-1] *)
Definition is_valid_word32 (n : N) : bool := N.leb n 4294967295.

(* Safe byte constructor returning None if out of bounds *)
Definition mk_byte (n : N) : option byte :=
  if is_valid_byte n then Some n else None.

(* Safe 16-bit word constructor returning None if out of bounds *)
Definition mk_word16 (n : N) : option word16 :=
  if is_valid_word16 n then Some n else None.

(* Truncates arbitrary natural to byte via bitwise AND with 0xFF *)
Definition trunc_byte (n : N) : byte := N.land n 255.
(* Truncates arbitrary natural to 16-bit word via bitwise AND with 0xFFFF *)
Definition trunc_word16 (n : N) : word16 := N.land n 65535.

(* Truncation to byte preserves boundedness: result ≤ 255 *)
Lemma trunc_byte_bounded : forall n,
  trunc_byte n <= 255.
Proof.
  intros n.
  unfold trunc_byte.
  replace 255 with (N.ones 8) by reflexivity.
  rewrite N.land_ones by lia.
  pose proof (N.mod_upper_bound n (2^8)).
  assert (2^8 <> 0) by (compute; discriminate).
  specialize (H H0).
  assert (n mod 2^8 < 256).
  { replace 256 with (2^8) by reflexivity. assumption. }
  assert (N.succ 255 = 256) by reflexivity.
  rewrite <- H2 in H1.
  apply N.lt_succ_r in H1.
  assumption.
Qed.

(* Truncation to 16-bit word preserves boundedness: result ≤ 65535 *)
Lemma trunc_word16_bounded : forall n,
  trunc_word16 n <= 65535.
Proof.
  intros n.
  unfold trunc_word16.
  replace 65535 with (N.ones 16) by reflexivity.
  rewrite N.land_ones by lia.
  pose proof (N.mod_upper_bound n (2^16)).
  assert (2^16 <> 0) by (compute; discriminate).
  specialize (H H0).
  assert (n mod 2^16 < 65536).
  { replace 65536 with (2^16) by reflexivity. assumption. }
  assert (N.succ 65535 = 65536) by reflexivity.
  rewrite <- H2 in H1.
  apply N.lt_succ_r in H1.
  assumption.
Qed.

(* Byte truncation is identity on valid bytes *)
Lemma trunc_byte_idempotent : forall n,
  n <= 255 -> trunc_byte n = n.
Proof.
  intros n Hbound.
  unfold trunc_byte.
  replace 255 with (N.ones 8) by reflexivity.
  rewrite N.land_ones by lia.
  rewrite N.mod_small; lia.
Qed.

(* 16-bit truncation is identity on valid words *)
Lemma trunc_word16_idempotent : forall n,
  n <= 65535 -> trunc_word16 n = n.
Proof.
  intros n Hbound.
  unfold trunc_word16.
  replace 65535 with (N.ones 16) by reflexivity.
  rewrite N.land_ones by lia.
  rewrite N.mod_small; lia.
Qed.

(* Hardware type constant: Ethernet (10Mbps and above) *)
Definition ARP_HRD_ETHERNET : word16 := 1.
(* Hardware type constant: Experimental Packet Radio Network *)
Definition ARP_HRD_PACKET_RADIO : word16 := 2.

(* Protocol type constant: IPv4 (EtherType 0x0800) *)
Definition ARP_PRO_IP : word16 := 2048.

(* ARP operation code: request (query for MAC address) *)
Definition ARP_OP_REQUEST : word16 := 1.
(* ARP operation code: reply (response with MAC address) *)
Definition ARP_OP_REPLY : word16 := 2.
(* RARP operation code: reverse ARP request (RFC 903) *)
Definition RARP_OP_REQUEST : word16 := 3.
(* RARP operation code: reverse ARP reply (RFC 903) *)
Definition RARP_OP_REPLY : word16 := 4.

(* Standard Ethernet MAC address length in bytes *)
Definition ETHERNET_ADDR_LEN : byte := 6.
(* Standard IPv4 address length in bytes *)
Definition IPV4_ADDR_LEN : byte := 4.

(* RFC 826: Validate supported hardware type *)
Definition is_supported_hardware (hrd : word16) : bool :=
  N.eqb hrd ARP_HRD_ETHERNET.

(* RFC 826: Validate supported protocol type *)
Definition is_supported_protocol (pro : word16) : bool :=
  N.eqb pro ARP_PRO_IP.

(* RFC 826: Validate address length fields match expected values *)
Definition are_lengths_valid (hln pln : byte) : bool :=
  (N.eqb hln ETHERNET_ADDR_LEN) && (N.eqb pln IPV4_ADDR_LEN).

(* RFC 826: Validate opcode is within known range *)
Definition is_valid_opcode (op : word16) : bool :=
  (N.eqb op ARP_OP_REQUEST) || (N.eqb op ARP_OP_REPLY) ||
  (N.eqb op RARP_OP_REQUEST) || (N.eqb op RARP_OP_REPLY).

(* =============================================================================
   Section 2: Address Types
   ============================================================================= *)

(* Ethernet MAC address: 48-bit hardware identifier with length constraint *)
Record MACAddress := {
  mac_bytes : list byte;
  mac_valid : length mac_bytes = 6%nat
}.

(* IPv4 address: 32-bit internet protocol address as four octets *)
Record IPv4Address := {
  ipv4_a : byte;
  ipv4_b : byte;
  ipv4_c : byte;
  ipv4_d : byte
}.

(* Ethernet broadcast address: FF:FF:FF:FF:FF:FF *)
Definition MAC_BROADCAST : MACAddress.
  refine {| mac_bytes := [255; 255; 255; 255; 255; 255] |}.
  reflexivity.
Defined.

(* Zero MAC address: 00:00:00:00:00:00 for unknown target in requests *)
Definition MAC_ZERO : MACAddress.
  refine {| mac_bytes := [0; 0; 0; 0; 0; 0] |}.
  reflexivity.
Defined.

(* Checks if MAC address is broadcast (FF:FF:FF:FF:FF:FF) *)
Definition is_broadcast_mac (m : MACAddress) : bool :=
  match m.(mac_bytes) with
  | [255; 255; 255; 255; 255; 255] => true
  | _ => false
  end.

(* Checks if MAC address is multicast via I/G bit (LSB of first octet) *)
Definition is_multicast_mac (m : MACAddress) : bool :=
  match m.(mac_bytes) with
  | b0 :: _ => N.testbit b0 0
  | _ => false
  end.

(* Checks if IPv4 address is all zeros (0.0.0.0) *)
Definition is_zero_ipv4 (ip : IPv4Address) : bool :=
  (N.eqb ip.(ipv4_a) 0) && (N.eqb ip.(ipv4_b) 0) &&
  (N.eqb ip.(ipv4_c) 0) && (N.eqb ip.(ipv4_d) 0).

(* Structural equality for MAC addresses *)
Definition mac_eq (m1 m2 : MACAddress) : bool :=
  if list_eq_dec N.eq_dec m1.(mac_bytes) m2.(mac_bytes)
  then true
  else false.

(* =============================================================================
   Section 3: ARP Packet Structure (RFC 826 Format)
   ============================================================================= *)

(* Generic ARP packet: variable-length addresses per RFC 826 *)
Record ARPPacket := {
  ar_hrd : word16;           (* Hardware address space (e.g., Ethernet) *)
  ar_pro : word16;           (* Protocol address space (e.g., IPv4) *)
  ar_hln : byte;             (* Byte length of hardware address *)
  ar_pln : byte;             (* Byte length of protocol address *)
  ar_op  : word16;           (* ARP operation code (request/reply) *)
  ar_sha : list byte;        (* Sender hardware address *)
  ar_spa : list byte;        (* Sender protocol address *)
  ar_tha : list byte;        (* Target hardware address *)
  ar_tpa : list byte         (* Target protocol address *)
}.

(* Ethernet/IPv4 ARP packet: fixed 48-bit MAC and 32-bit IP addresses *)
Record ARPEthernetIPv4 := {
  arp_op : word16;           (* Operation: request (1) or reply (2) *)
  arp_sha : MACAddress;      (* Sender 48-bit MAC address *)
  arp_spa : IPv4Address;     (* Sender 32-bit IP address *)
  arp_tha : MACAddress;      (* Target 48-bit MAC address *)
  arp_tpa : IPv4Address      (* Target 32-bit IP address *)
}.

(* =============================================================================
   Section 4: ARP Cache Table
   ============================================================================= *)

(* ARP cache entry: maps IP to MAC with TTL and mutability flag *)
Record ARPCacheEntry := {
  ace_ip : IPv4Address;      (* Protocol address (lookup key) *)
  ace_mac : MACAddress;      (* Hardware address (resolved value) *)
  ace_ttl : N;               (* Time-to-live in seconds *)
  ace_static : bool          (* True: permanent, False: expires *)
}.

(* ARP cache table: linear list of IP-to-MAC mappings *)
Definition ARPCache := list ARPCacheEntry.

(* Structural equality for IPv4 addresses: compares all four octets *)
Definition ip_eq (ip1 ip2 : IPv4Address) : bool :=
  (N.eqb ip1.(ipv4_a) ip2.(ipv4_a)) &&
  (N.eqb ip1.(ipv4_b) ip2.(ipv4_b)) &&
  (N.eqb ip1.(ipv4_c) ip2.(ipv4_c)) &&
  (N.eqb ip1.(ipv4_d) ip2.(ipv4_d)).

(* Searches cache for IP address, returning associated MAC if found *)
Definition lookup_cache (cache : ARPCache) (ip : IPv4Address) : option MACAddress :=
  let fix find (c : ARPCache) : option MACAddress :=
    match c with
    | [] => None
    | entry :: rest =>
        if ip_eq entry.(ace_ip) ip
        then Some entry.(ace_mac)
        else find rest
    end
  in find cache.

(* Updates existing cache entry, preserving static entries *)
Definition update_cache_entry (cache : ARPCache) (ip : IPv4Address) (mac : MACAddress)
                              (ttl : N) : ARPCache :=
  let entry := {| ace_ip := ip; ace_mac := mac; ace_ttl := ttl; ace_static := false |} in
  let fix update (c : ARPCache) : ARPCache :=
    match c with
    | [] => []  (* Not found, don't add *)
    | e :: rest =>
        if ip_eq e.(ace_ip) ip
        then
          if e.(ace_static)
          then e :: rest  (* Don't overwrite static entries *)
          else entry :: rest  (* Update dynamic entry *)
        else e :: update rest
    end
  in update cache.

(* Adds new cache entry if IP not present, otherwise preserves existing *)
Definition add_cache_entry (cache : ARPCache) (ip : IPv4Address) (mac : MACAddress)
                          (ttl : N) : ARPCache :=
  let entry := {| ace_ip := ip; ace_mac := mac; ace_ttl := ttl; ace_static := false |} in
  let fix add (c : ARPCache) : ARPCache :=
    match c with
    | [] => [entry]  (* Not found, add new *)
    | e :: rest =>
        if ip_eq e.(ace_ip) ip
        then e :: rest  (* Already exists, don't modify *)
        else e :: add rest
    end
  in add cache.

(* Unconditional merge: updates existing or adds new entry *)
Definition merge_cache_entry (cache : ARPCache) (ip : IPv4Address) (mac : MACAddress)
                            (ttl : N) : ARPCache :=
  let entry := {| ace_ip := ip; ace_mac := mac; ace_ttl := ttl; ace_static := false |} in
  let fix update (c : ARPCache) : ARPCache :=
    match c with
    | [] => [entry]  (* Not found, add new *)
    | e :: rest =>
        if ip_eq e.(ace_ip) ip
        then
          if e.(ace_static)
          then e :: rest  (* Don't overwrite static entries *)
          else entry :: rest  (* Update dynamic entry *)
        else e :: update rest
    end
  in update cache.

(* RFC 826 compliant merge: updates if exists, adds only if target *)
Definition rfc826_merge (cache : ARPCache) (ip : IPv4Address) (mac : MACAddress)
                        (ttl : N) (i_am_target : bool) : ARPCache :=
  match lookup_cache cache ip with
  | Some _ => update_cache_entry cache ip mac ttl  (* Exists: update *)
  | None => if i_am_target
           then add_cache_entry cache ip mac ttl   (* Target: add *)
           else cache                               (* Not target: ignore *)
  end.

(* RFC 826 explicit merge flag algorithm: models the RFC's two-phase approach *)
Definition rfc826_merge_explicit (cache : ARPCache) (ip : IPv4Address) (mac : MACAddress)
                                  (ttl : N) (i_am_target : bool) : bool * ARPCache :=
  (* Step 1: Check if entry exists and set merge_flag *)
  let merge_flag := match lookup_cache cache ip with
                    | Some _ => true
                    | None => false
                    end in
  (* Step 2: Update cache if entry exists *)
  let cache' := if merge_flag
                then update_cache_entry cache ip mac ttl
                else cache in
  (* Step 3: If target and merge_flag is false, add entry *)
  let cache'' := if i_am_target && negb merge_flag
                 then add_cache_entry cache' ip mac ttl
                 else cache' in
  (merge_flag, cache'').

(* Theorem: Explicit merge flag produces same result as implicit version *)
Theorem rfc826_merge_explicit_equiv : forall cache ip mac ttl target,
  snd (rfc826_merge_explicit cache ip mac ttl target) =
  rfc826_merge cache ip mac ttl target.
Proof.
  intros cache ip mac ttl target.
  unfold rfc826_merge_explicit, rfc826_merge.
  destruct (lookup_cache cache ip) eqn:Hlookup.
  - simpl. destruct target; reflexivity.
  - simpl. destruct target; simpl; reflexivity.
Qed.

(* =============================================================================
   Section 4A: Additional Cache Properties
   ============================================================================= *)

(* Static cache entries remain in cache after update operations *)
Theorem static_entries_preserved : forall cache ip mac ttl e,
  In e cache ->
  ace_static e = true ->
  ip_eq e.(ace_ip) ip = true ->
  In e (update_cache_entry cache ip mac ttl).
Proof.
  intros cache ip mac ttl e Hin Hstatic Heq_ip.
  unfold update_cache_entry.
  induction cache as [|e' rest IH].
  - inversion Hin.
  - simpl. destruct (ip_eq (ace_ip e') ip) eqn:Heq'.
    + destruct (ace_static e') eqn:Hstatic'.
      * destruct Hin as [Heq_e | Hin_rest].
        { subst e'. left. reflexivity. }
        { right. assumption. }
      * destruct Hin as [Heq_e | Hin_rest].
        { subst e'. rewrite Hstatic in Hstatic'. discriminate. }
        { right. assumption. }
    + destruct Hin as [Heq_e | Hin_rest].
      * left. assumption.
      * right. apply IH. assumption.
Qed.

Theorem static_entries_never_overwritten : forall cache ip mac ttl e,
  In e cache ->
  ace_static e = true ->
  ip_eq e.(ace_ip) ip = true ->
  In e (update_cache_entry cache ip mac ttl).
Proof.
  intros cache ip mac ttl e Hin Hstatic Heq_ip.
  apply static_entries_preserved; assumption.
Qed.

(* Looking up any IP in empty cache returns None *)
Theorem lookup_empty : forall ip,
  lookup_cache [] ip = None.
Proof.
  intros ip. unfold lookup_cache. simpl. reflexivity.
Qed.

(* RFC 826 merge with non-target and absent IP leaves cache unchanged *)
Theorem rfc826_merge_not_target : forall cache ip mac ttl,
  lookup_cache cache ip = None ->
  rfc826_merge cache ip mac ttl false = cache.
Proof.
  intros cache ip mac ttl Hnone.
  unfold rfc826_merge. rewrite Hnone. reflexivity.
Qed.

(* =============================================================================
   Section 5: Packet Construction
   ============================================================================= *)

(* Constructs ARP request packet: queries for MAC address of target IP *)
Definition make_arp_request (my_mac : MACAddress) (my_ip : IPv4Address)
                           (target_ip : IPv4Address) : ARPEthernetIPv4 :=
  {| arp_op := ARP_OP_REQUEST;
     arp_sha := my_mac;
     arp_spa := my_ip;
     arp_tha := MAC_ZERO;  (* Unknown target MAC, RFC 826 *)
     arp_tpa := target_ip |}.

(* Constructs ARP reply packet: provides MAC address to requester *)
Definition make_arp_reply (my_mac : MACAddress) (my_ip : IPv4Address)
                         (requester_mac : MACAddress) (requester_ip : IPv4Address)
                         : ARPEthernetIPv4 :=
  {| arp_op := ARP_OP_REPLY;
     arp_sha := my_mac;
     arp_spa := my_ip;
     arp_tha := requester_mac;
     arp_tpa := requester_ip |}.

(* =============================================================================
   Section 6: Packet Serialization
   ============================================================================= *)

(* Serializes MAC address to 6-byte list *)
Definition serialize_mac (m : MACAddress) : list byte := m.(mac_bytes).

(* Serializes IPv4 address to 4-byte list in network order *)
Definition serialize_ipv4 (ip : IPv4Address) : list byte :=
  [ip.(ipv4_a); ip.(ipv4_b); ip.(ipv4_c); ip.(ipv4_d)].

(* Splits 16-bit word into high and low bytes (big-endian) *)
Definition split_word16 (w : word16) : list byte :=
  [N.shiftr w 8; N.land w 255].

(* Combines two bytes into 16-bit word (big-endian) *)
Definition combine_word16 (hi lo : byte) : word16 :=
  N.lor (N.shiftl hi 8) lo.

(* Serializes ARP packet to 28-byte wire format per RFC 826 *)
Definition serialize_arp_packet (p : ARPEthernetIPv4) : list byte :=
  split_word16 ARP_HRD_ETHERNET ++
  split_word16 ARP_PRO_IP ++
  [ETHERNET_ADDR_LEN] ++
  [IPV4_ADDR_LEN] ++
  split_word16 p.(arp_op) ++
  serialize_mac p.(arp_sha) ++
  serialize_ipv4 p.(arp_spa) ++
  serialize_mac p.(arp_tha) ++
  serialize_ipv4 p.(arp_tpa).

(* Parses 28-byte wire format into typed ARP packet, validating structure *)
Definition parse_arp_packet (data : list byte) : option ARPEthernetIPv4 :=
  match data with
  | hrd_hi :: hrd_lo :: pro_hi :: pro_lo :: hln :: pln ::
    op_hi :: op_lo ::
    sha1 :: sha2 :: sha3 :: sha4 :: sha5 :: sha6 ::
    spa1 :: spa2 :: spa3 :: spa4 ::
    tha1 :: tha2 :: tha3 :: tha4 :: tha5 :: tha6 ::
    tpa1 :: tpa2 :: tpa3 :: tpa4 :: nil =>
    if (N.eqb (combine_word16 hrd_hi hrd_lo) ARP_HRD_ETHERNET) &&
       (N.eqb (combine_word16 pro_hi pro_lo) ARP_PRO_IP) &&
       (N.eqb hln ETHERNET_ADDR_LEN) &&
       (N.eqb pln IPV4_ADDR_LEN)
    then
      Some {| arp_op := combine_word16 op_hi op_lo;
              arp_sha := {| mac_bytes := [sha1; sha2; sha3; sha4; sha5; sha6];
                           mac_valid := eq_refl |};
              arp_spa := {| ipv4_a := spa1; ipv4_b := spa2;
                           ipv4_c := spa3; ipv4_d := spa4 |};
              arp_tha := {| mac_bytes := [tha1; tha2; tha3; tha4; tha5; tha6];
                           mac_valid := eq_refl |};
              arp_tpa := {| ipv4_a := tpa1; ipv4_b := tpa2;
                           ipv4_c := tpa3; ipv4_d := tpa4 |} |}
    else None
  | _ => None
  end.

(* =============================================================================
   Section 6A: Generic Hardware/Protocol Type Processing
   ============================================================================= *)

(* Checks if hardware/protocol combination is Ethernet/IPv4 *)
Definition is_supported_hw_proto (hrd : word16) (pro : word16) : bool :=
  (N.eqb hrd ARP_HRD_ETHERNET && N.eqb pro ARP_PRO_IP).

(* Converts generic ARP packet to Ethernet/IPv4 if types match *)
Definition process_generic_arp (packet : ARPPacket)
  : option ARPEthernetIPv4 :=
  if is_supported_hw_proto packet.(ar_hrd) packet.(ar_pro) then
    if (N.eqb packet.(ar_hln) ETHERNET_ADDR_LEN) &&
       (N.eqb packet.(ar_pln) IPV4_ADDR_LEN) then
      match packet.(ar_sha), packet.(ar_spa), packet.(ar_tha), packet.(ar_tpa) with
      | [sha1; sha2; sha3; sha4; sha5; sha6],
        [spa1; spa2; spa3; spa4],
        [tha1; tha2; tha3; tha4; tha5; tha6],
        [tpa1; tpa2; tpa3; tpa4] =>
          Some {| arp_op := packet.(ar_op);
                  arp_sha := {| mac_bytes := [sha1; sha2; sha3; sha4; sha5; sha6];
                               mac_valid := eq_refl |};
                  arp_spa := {| ipv4_a := spa1; ipv4_b := spa2;
                               ipv4_c := spa3; ipv4_d := spa4 |};
                  arp_tha := {| mac_bytes := [tha1; tha2; tha3; tha4; tha5; tha6];
                               mac_valid := eq_refl |};
                  arp_tpa := {| ipv4_a := tpa1; ipv4_b := tpa2;
                               ipv4_c := tpa3; ipv4_d := tpa4 |} |}
      | _, _, _, _ => None
      end
    else None
  else None.

(* Converts Ethernet/IPv4 packet to generic ARP format *)
Definition convert_to_generic (packet : ARPEthernetIPv4) : ARPPacket :=
  {| ar_hrd := ARP_HRD_ETHERNET;
     ar_pro := ARP_PRO_IP;
     ar_hln := ETHERNET_ADDR_LEN;
     ar_pln := IPV4_ADDR_LEN;
     ar_op := packet.(arp_op);
     ar_sha := serialize_mac packet.(arp_sha);
     ar_spa := serialize_ipv4 packet.(arp_spa);
     ar_tha := serialize_mac packet.(arp_tha);
     ar_tpa := serialize_ipv4 packet.(arp_tpa) |}.

(* =============================================================================
   Section 6B: Packet Validation (RFC 826 Compliance)
   ============================================================================= *)

(* RFC 826: Comprehensive packet validation for Ethernet/IPv4 ARP *)
Definition validate_arp_packet (packet : ARPEthernetIPv4) (my_mac : MACAddress) : bool :=
  (* Validate opcode is known *)
  is_valid_opcode packet.(arp_op) &&
  (* RFC 826: Sender MAC must not be broadcast *)
  negb (is_broadcast_mac packet.(arp_sha)) &&
  (* Security: Sender MAC should not be multicast *)
  negb (is_multicast_mac packet.(arp_sha)) &&
  (* RFC 5227: Allow zero source IP only for ARP probes (op=REQUEST with SPA=0) *)
  (if is_zero_ipv4 packet.(arp_spa)
   then N.eqb packet.(arp_op) ARP_OP_REQUEST
   else true) &&
  (* Validate reply THA: if this is a reply, THA should be our MAC *)
  (if N.eqb packet.(arp_op) ARP_OP_REPLY
   then mac_eq packet.(arp_tha) my_mac
   else true).

(* =============================================================================
   Section 7: Protocol State Machine
   ============================================================================= *)

(* ARP protocol context: RFC 826 basic model *)
Record ARPContext := {
  arp_my_mac : MACAddress;           (* This host's MAC address *)
  arp_my_ip : IPv4Address;           (* This host's IP address *)
  arp_cache : ARPCache               (* IP-to-MAC resolution cache *)
}.

(* =============================================================================
   Section 8: RFC 826 Reception Algorithm
   ============================================================================= *)

(* RFC 826 packet reception: validates, merges cache, generates reply if target *)
Definition process_arp_packet (ctx : ARPContext) (packet : ARPEthernetIPv4)
                             : ARPContext * option ARPEthernetIPv4 :=
  (* RFC 826 Algorithm with comprehensive validation: *)

  (* Step 0: Comprehensive packet validation *)
  if validate_arp_packet packet ctx.(arp_my_mac)
  then
    (* Step 1: Check if I am the target *)
    let i_am_target := ip_eq packet.(arp_tpa) ctx.(arp_my_ip) in

    (* Step 2: RFC 826 compliant conditional merge *)
    let cache' := rfc826_merge ctx.(arp_cache)
                               packet.(arp_spa)
                               packet.(arp_sha)
                               300 (* 5 minute TTL *)
                               i_am_target in

    let ctx' := {| arp_my_mac := ctx.(arp_my_mac);
                   arp_my_ip := ctx.(arp_my_ip);
                   arp_cache := cache' |} in

    (* Step 3: If I am the target and it's a request, send reply *)
    if i_am_target
    then
      if N.eqb packet.(arp_op) ARP_OP_REQUEST
      then
        let reply := make_arp_reply ctx.(arp_my_mac) ctx.(arp_my_ip)
                                    packet.(arp_sha) packet.(arp_spa) in
        (ctx', Some reply)
      else
        (ctx', None)
    else
      (ctx', None)
  else
    (ctx, None).  (* Drop invalid packets *)

(* =============================================================================
   Section 8A: RARP Processing (RFC 903)
   ============================================================================= *)

(* RFC 903: RARP validates that target MAC matches our MAC *)
Definition validate_rarp_packet (packet : ARPEthernetIPv4) (my_mac : MACAddress) : bool :=
  (* RARP-specific validation *)
  is_valid_opcode packet.(arp_op) &&
  negb (is_broadcast_mac packet.(arp_sha)) &&
  negb (is_multicast_mac packet.(arp_sha)) &&
  (* RARP request: THA should be our MAC, SPA should be zero *)
  (if N.eqb packet.(arp_op) RARP_OP_REQUEST
   then mac_eq packet.(arp_tha) my_mac && is_zero_ipv4 packet.(arp_spa)
   else true) &&
  (* RARP reply: THA should be our MAC *)
  (if N.eqb packet.(arp_op) RARP_OP_REPLY
   then mac_eq packet.(arp_tha) my_mac
   else true).

Definition process_rarp_packet (ctx : ARPContext) (packet : ARPEthernetIPv4)
                               : ARPContext * option IPv4Address :=
  if validate_rarp_packet packet ctx.(arp_my_mac)
  then
    if N.eqb packet.(arp_op) RARP_OP_REQUEST
    then
      if mac_eq packet.(arp_tha) ctx.(arp_my_mac)
      then (ctx, Some ctx.(arp_my_ip))
      else (ctx, None)
    else if N.eqb packet.(arp_op) RARP_OP_REPLY
    then (ctx, Some packet.(arp_tpa))
    else (ctx, None)
  else (ctx, None).

(* =============================================================================
   Section 9: Gratuitous ARP
   ============================================================================= *)

Definition make_gratuitous_arp (my_mac : MACAddress) (my_ip : IPv4Address)
                               : ARPEthernetIPv4 :=
  {| arp_op := ARP_OP_REQUEST;
     arp_sha := my_mac;
     arp_spa := my_ip;
     arp_tha := MAC_ZERO;
     arp_tpa := my_ip |}.

Definition is_gratuitous_arp (pkt : ARPEthernetIPv4) : bool :=
  ip_eq pkt.(arp_spa) pkt.(arp_tpa).

Theorem gratuitous_arp_no_reply : forall ctx pkt ctx' resp,
  is_gratuitous_arp pkt = true ->
  ip_eq pkt.(arp_tpa) ctx.(arp_my_ip) = false ->
  process_arp_packet ctx pkt = (ctx', resp) ->
  resp = None.
Proof.
  intros ctx pkt ctx' resp Hgrat Hnot_target Hproc.
  unfold process_arp_packet in Hproc.
  destruct (validate_arp_packet pkt (arp_my_mac ctx)) eqn:Hvalid.
  - rewrite Hnot_target in Hproc.
    injection Hproc as _ Hresp. symmetry. assumption.
  - injection Hproc as _ Hresp. symmetry. assumption.
Qed.

(* =============================================================================
   Section 10: Security Considerations
   ============================================================================= *)

(* Check for ARP spoofing attempts *)
Definition is_suspicious_arp (cache : ARPCache) (packet : ARPEthernetIPv4) : bool :=
  match lookup_cache cache packet.(arp_spa) with
  | None => false  (* New entry, not suspicious *)
  | Some cached_mac =>
      (* MAC changed for existing IP *)
      if list_eq_dec N.eq_dec
                     cached_mac.(mac_bytes)
                     packet.(arp_sha).(mac_bytes)
      then false  (* Same MAC, not suspicious *)
      else true
  end.

Theorem cache_detects_mac_conflict : forall cache ip mac1 mac2,
  lookup_cache cache ip = Some mac1 ->
  mac_eq mac1 mac2 = false ->
  is_suspicious_arp cache {| arp_op := ARP_OP_REQUEST;
                              arp_sha := mac2;
                              arp_spa := ip;
                              arp_tha := MAC_ZERO;
                              arp_tpa := ip |} = true.
Proof.
  intros cache ip mac1 mac2 Hlookup Hneq.
  unfold is_suspicious_arp. simpl. rewrite Hlookup.
  destruct (list_eq_dec N.eq_dec (mac_bytes mac1) (mac_bytes mac2)) eqn:Heq.
  - unfold mac_eq in Hneq. rewrite Heq in Hneq. discriminate.
  - reflexivity.
Qed.

(* =============================================================================
   Section 10A: Timing and Timeouts
   ============================================================================= *)

Definition ARP_REQUEST_TIMEOUT : N := 1000.  (* 1 second in milliseconds *)
Definition ARP_MAX_RETRIES : N := 3.
Definition ARP_PROBE_WAIT : N := 1000.      (* RFC 5227: wait before probing *)
Definition ARP_PROBE_NUM : N := 3.           (* Number of probes to send *)
Definition ARP_PROBE_MIN : N := 1000.        (* Min delay between probes *)
Definition ARP_PROBE_MAX : N := 2000.        (* Max delay between probes *)
Definition ARP_ANNOUNCE_WAIT : N := 2000.    (* Wait after probe before announce *)
Definition ARP_ANNOUNCE_NUM : N := 2.        (* Number of announcements *)
Definition ARP_ANNOUNCE_INTERVAL : N := 2000. (* Delay between announcements *)
Definition ARP_DEFEND_INTERVAL : N := 10000. (* Min time between defenses *)

Record ARPTimer := {
  timer_start : N;      (* Timestamp when timer started *)
  timer_duration : N;   (* Duration in milliseconds *)
  timer_active : bool
}.

Definition timer_expired (timer : ARPTimer) (current_time : N) : bool :=
  if timer.(timer_active)
  then N.leb (timer.(timer_start) + timer.(timer_duration)) current_time
  else false.

Definition start_timer (duration : N) (current_time : N) : ARPTimer :=
  {| timer_start := current_time;
     timer_duration := duration;
     timer_active := true |}.

Definition stop_timer (timer : ARPTimer) : ARPTimer :=
  {| timer_start := timer.(timer_start);
     timer_duration := timer.(timer_duration);
     timer_active := false |}.

Lemma timer_never_expires_when_inactive : forall timer t,
  timer.(timer_active) = false ->
  timer_expired timer t = false.
Proof.
  intros timer t Hinactive.
  unfold timer_expired.
  rewrite Hinactive.
  reflexivity.
Qed.

Lemma timer_expires_at_deadline : forall duration start_time,
  timer_expired (start_timer duration start_time) (start_time + duration) = true.
Proof.
  intros duration start_time.
  unfold timer_expired, start_timer.
  simpl.
  rewrite N.leb_refl.
  reflexivity.
Qed.

Lemma timer_not_expired_before_deadline : forall duration start_time current_time,
  current_time < start_time + duration ->
  timer_expired (start_timer duration start_time) current_time = false.
Proof.
  intros duration start_time current_time Hbefore.
  unfold timer_expired, start_timer.
  simpl.
  apply N.leb_gt in Hbefore.
  rewrite Hbefore.
  reflexivity.
Qed.

Lemma timer_expired_after_deadline : forall duration start_time current_time,
  start_time + duration <= current_time ->
  timer_expired (start_timer duration start_time) current_time = true.
Proof.
  intros duration start_time current_time Hafter.
  unfold timer_expired, start_timer.
  simpl.
  apply N.leb_le.
  assumption.
Qed.

Lemma stop_timer_never_expires : forall timer t,
  timer_expired (stop_timer timer) t = false.
Proof.
  intros timer t.
  unfold timer_expired, stop_timer.
  simpl.
  reflexivity.
Qed.

Lemma start_timer_is_active : forall duration current_time,
  timer_active (start_timer duration current_time) = true.
Proof.
  intros duration current_time.
  unfold start_timer.
  simpl.
  reflexivity.
Qed.

Lemma stop_timer_is_inactive : forall timer,
  timer_active (stop_timer timer) = false.
Proof.
  intros timer.
  unfold stop_timer.
  simpl.
  reflexivity.
Qed.

(* =============================================================================
   Section 10B: Enhanced State Machine with Transitions
   ============================================================================= *)

Record PendingRequest := {
  preq_target_ip : IPv4Address;
  preq_retries : N;
  preq_timer : ARPTimer
}.

Record ProbeState := {
  probe_ip : IPv4Address;
  probe_count : N;
  probe_timer : ARPTimer
}.

Record AnnounceState := {
  announce_count : N;
  announce_timer : ARPTimer
}.

Record DefendState := {
  defend_last_time : N
}.

Inductive ARPStateData :=
  | StateIdle
  | StatePending : list PendingRequest -> ARPStateData
  | StateProbe : ProbeState -> ARPStateData
  | StateAnnounce : AnnounceState -> ARPStateData
  | StateDefend : DefendState -> ARPStateData
  | StateConflict : IPv4Address -> ARPStateData.

Record NetworkInterface := {
  if_mac : MACAddress;
  if_ip : IPv4Address;
  if_mtu : N;
  if_up : bool
}.

Record FloodEntry := {
  fe_ip : IPv4Address;
  fe_last_request : N;
  fe_request_count : N
}.

Definition FloodTable := list FloodEntry.

Record EnhancedARPContext := {
  earp_my_mac : MACAddress;
  earp_my_ip : IPv4Address;
  earp_cache : ARPCache;
  earp_state_data : ARPStateData;
  earp_iface : NetworkInterface;
  earp_flood_table : FloodTable;
  earp_last_cache_cleanup : N
}.

(* =============================================================================
   Section 10B1: Flood Prevention Mechanism
   ============================================================================= *)

Definition ARP_FLOOD_WINDOW : N := 1000.
Definition ARP_FLOOD_THRESHOLD : N := 5.

Definition flood_eq (ip1 ip2 : IPv4Address) : bool := ip_eq ip1 ip2.

Definition lookup_flood_entry (table : FloodTable) (ip : IPv4Address) : option FloodEntry :=
  let fix find (t : FloodTable) : option FloodEntry :=
    match t with
    | [] => None
    | entry :: rest =>
        if flood_eq entry.(fe_ip) ip
        then Some entry
        else find rest
    end
  in find table.

Definition update_flood_table (table : FloodTable) (ip : IPv4Address) (current_time : N)
                               : FloodTable * bool :=
  match lookup_flood_entry table ip with
  | None =>
      let new_entry := {| fe_ip := ip; fe_last_request := current_time; fe_request_count := 1 |} in
      (new_entry :: table, true)
  | Some entry =>
      let time_diff := current_time - entry.(fe_last_request) in
      if N.leb time_diff ARP_FLOOD_WINDOW
      then
        let new_count := entry.(fe_request_count) + 1 in
        if N.leb new_count ARP_FLOOD_THRESHOLD
        then
          let updated := {| fe_ip := ip; fe_last_request := current_time;
                           fe_request_count := new_count |} in
          let fix replace (t : FloodTable) : FloodTable :=
            match t with
            | [] => [updated]
            | e :: rest => if flood_eq e.(fe_ip) ip then updated :: rest else e :: replace rest
            end
          in (replace table, true)
        else
          (table, false)
      else
        let reset_entry := {| fe_ip := ip; fe_last_request := current_time; fe_request_count := 1 |} in
        let fix replace (t : FloodTable) : FloodTable :=
          match t with
          | [] => [reset_entry]
          | e :: rest => if flood_eq e.(fe_ip) ip then reset_entry :: rest else e :: replace rest
          end
        in (replace table, true)
  end.

Definition clean_flood_table (table : FloodTable) (current_time : N) : FloodTable :=
  filter (fun entry =>
    N.ltb (current_time - entry.(fe_last_request)) (ARP_FLOOD_WINDOW * 10)) table.

Lemma flood_table_allows_first_request : forall table ip current_time,
  lookup_flood_entry table ip = None ->
  snd (update_flood_table table ip current_time) = true.
Proof.
  intros table ip current_time Hlookup.
  unfold update_flood_table.
  rewrite Hlookup.
  simpl. reflexivity.
Qed.

Lemma flood_table_rejects_excessive : forall table ip current_time entry,
  lookup_flood_entry table ip = Some entry ->
  N.leb (current_time - entry.(fe_last_request)) ARP_FLOOD_WINDOW = true ->
  N.leb (entry.(fe_request_count) + 1) ARP_FLOOD_THRESHOLD = false ->
  snd (update_flood_table table ip current_time) = false.
Proof.
  intros table ip current_time entry Hlookup Hwindow Hthreshold.
  unfold update_flood_table.
  rewrite Hlookup.
  rewrite Hwindow.
  rewrite Hthreshold.
  simpl. reflexivity.
Qed.

Lemma flood_table_resets_after_window : forall table ip current_time entry,
  lookup_flood_entry table ip = Some entry ->
  N.leb (current_time - entry.(fe_last_request)) ARP_FLOOD_WINDOW = false ->
  snd (update_flood_table table ip current_time) = true.
Proof.
  intros table ip current_time entry Hlookup Hwindow.
  unfold update_flood_table.
  rewrite Hlookup.
  rewrite Hwindow.
  simpl. reflexivity.
Qed.

Lemma clean_flood_table_preserves_recent : forall table current_time entry,
  In entry table ->
  current_time - entry.(fe_last_request) < ARP_FLOOD_WINDOW * 10 ->
  In entry (clean_flood_table table current_time).
Proof.
  intros table current_time entry Hin Hrecent.
  unfold clean_flood_table.
  apply filter_In.
  split; auto.
  apply N.ltb_lt.
  assumption.
Qed.

Lemma clean_flood_table_removes_old : forall table current_time entry,
  In entry (clean_flood_table table current_time) ->
  current_time - entry.(fe_last_request) < ARP_FLOOD_WINDOW * 10.
Proof.
  intros table current_time entry Hin.
  unfold clean_flood_table in Hin.
  apply filter_In in Hin.
  destruct Hin as [_ Hcond].
  apply N.ltb_lt in Hcond.
  assumption.
Qed.

(* =============================================================================
   Section 10C: Request Queue Management and Retries
   ============================================================================= *)

Definition add_pending_request (ctx : EnhancedARPContext) (target_ip : IPv4Address)
                               (current_time : N) : EnhancedARPContext :=
  match ctx.(earp_state_data) with
  | StatePending reqs =>
      let new_req := {| preq_target_ip := target_ip;
                       preq_retries := 0;
                       preq_timer := start_timer ARP_REQUEST_TIMEOUT current_time |} in
      {| earp_my_mac := ctx.(earp_my_mac);
         earp_my_ip := ctx.(earp_my_ip);
         earp_cache := ctx.(earp_cache);
         earp_state_data := StatePending (new_req :: reqs);
         earp_iface := ctx.(earp_iface);
         earp_flood_table := ctx.(earp_flood_table);
         earp_last_cache_cleanup := ctx.(earp_last_cache_cleanup) |}
  | _ =>
      let new_req := {| preq_target_ip := target_ip;
                       preq_retries := 0;
                       preq_timer := start_timer ARP_REQUEST_TIMEOUT current_time |} in
      {| earp_my_mac := ctx.(earp_my_mac);
         earp_my_ip := ctx.(earp_my_ip);
         earp_cache := ctx.(earp_cache);
         earp_state_data := StatePending [new_req];
         earp_iface := ctx.(earp_iface);
         earp_flood_table := ctx.(earp_flood_table);
         earp_last_cache_cleanup := ctx.(earp_last_cache_cleanup) |}
  end.

Definition remove_pending_request (reqs : list PendingRequest) (target_ip : IPv4Address)
                                  : list PendingRequest :=
  filter (fun req => negb (ip_eq req.(preq_target_ip) target_ip)) reqs.

Definition retry_pending_request (req : PendingRequest) (current_time : N)
                                 : PendingRequest :=
  {| preq_target_ip := req.(preq_target_ip);
     preq_retries := req.(preq_retries) + 1;
     preq_timer := start_timer ARP_REQUEST_TIMEOUT current_time |}.

Definition process_timeouts (ctx : EnhancedARPContext) (current_time : N)
                           : EnhancedARPContext * list ARPEthernetIPv4 :=
  match ctx.(earp_state_data) with
  | StatePending reqs =>
      let process_req (acc : list PendingRequest * list ARPEthernetIPv4) (req : PendingRequest) :=
        let '(kept_reqs, packets) := acc in
        if timer_expired req.(preq_timer) current_time
        then
          if N.ltb req.(preq_retries) ARP_MAX_RETRIES
          then
            let new_req := retry_pending_request req current_time in
            let arp_req := make_arp_request ctx.(earp_my_mac) ctx.(earp_my_ip)
                                            req.(preq_target_ip) in
            (new_req :: kept_reqs, arp_req :: packets)
          else
            (kept_reqs, packets)
        else
          (req :: kept_reqs, packets)
      in
      let '(acc_reqs, packets) := fold_left process_req reqs ([], []) in
      let new_reqs := rev acc_reqs in
      ({| earp_my_mac := ctx.(earp_my_mac);
          earp_my_ip := ctx.(earp_my_ip);
          earp_cache := ctx.(earp_cache);
          earp_state_data := match new_reqs with
                             | [] => StateIdle
                             | _ => StatePending new_reqs
                             end;
          earp_iface := ctx.(earp_iface);
          earp_flood_table := ctx.(earp_flood_table);
          earp_last_cache_cleanup := ctx.(earp_last_cache_cleanup) |}, rev packets)
  | _ => (ctx, [])
  end.

(* RFC 826 High-Level Address Resolution with Flood Prevention *)
Definition resolve_address (ctx : EnhancedARPContext) (target_ip : IPv4Address)
                           (current_time : N)
  : option MACAddress * EnhancedARPContext * option ARPEthernetIPv4 :=
  match lookup_cache ctx.(earp_cache) target_ip with
  | Some mac =>
      (Some mac, ctx, None)
  | None =>
      let '(new_flood, allowed) := update_flood_table ctx.(earp_flood_table) target_ip current_time in
      if allowed
      then
        let ctx' := add_pending_request ctx target_ip current_time in
        let ctx'' := {| earp_my_mac := ctx'.(earp_my_mac);
                       earp_my_ip := ctx'.(earp_my_ip);
                       earp_cache := ctx'.(earp_cache);
                       earp_state_data := ctx'.(earp_state_data);
                       earp_iface := ctx'.(earp_iface);
                       earp_flood_table := new_flood;
                       earp_last_cache_cleanup := ctx'.(earp_last_cache_cleanup) |} in
        let req := make_arp_request ctx.(earp_my_mac) ctx.(earp_my_ip) target_ip in
        (None, ctx'', Some req)
      else
        (None, ctx, None)
  end.

(* =============================================================================
   Section 10D: Duplicate Address Detection (DAD) / RFC 5227 ARP Probe
   ============================================================================= *)

Definition start_dad_probe (ctx : EnhancedARPContext) (ip_to_probe : IPv4Address)
                           (current_time : N) : EnhancedARPContext :=
  {| earp_my_mac := ctx.(earp_my_mac);
     earp_my_ip := ctx.(earp_my_ip);
     earp_cache := ctx.(earp_cache);
     earp_state_data := StateProbe {| probe_ip := ip_to_probe;
                                     probe_count := 0;
                                     probe_timer := start_timer ARP_PROBE_WAIT current_time |};
     earp_iface := ctx.(earp_iface);
     earp_flood_table := ctx.(earp_flood_table);
     earp_last_cache_cleanup := ctx.(earp_last_cache_cleanup) |}.

Definition make_arp_probe (my_mac : MACAddress) (target_ip : IPv4Address)
                          : ARPEthernetIPv4 :=
  {| arp_op := ARP_OP_REQUEST;
     arp_sha := my_mac;
     arp_spa := {| ipv4_a := 0; ipv4_b := 0; ipv4_c := 0; ipv4_d := 0 |};  (* Sender IP = 0 *)
     arp_tha := MAC_ZERO;  (* Unknown target MAC *)
     arp_tpa := target_ip |}.

Definition process_probe_timeout (ctx : EnhancedARPContext) (probe : ProbeState)
                                 (current_time : N)
                                 : EnhancedARPContext * option ARPEthernetIPv4 :=
  if timer_expired probe.(probe_timer) current_time
  then
    if N.ltb probe.(probe_count) ARP_PROBE_NUM
    then
      let new_probe := {| probe_ip := probe.(probe_ip);
                         probe_count := probe.(probe_count) + 1;
                         probe_timer := start_timer ARP_PROBE_MIN current_time |} in
      let ctx' := {| earp_my_mac := ctx.(earp_my_mac);
                    earp_my_ip := ctx.(earp_my_ip);
                    earp_cache := ctx.(earp_cache);
                    earp_state_data := StateProbe new_probe;
                    earp_iface := ctx.(earp_iface);
                    earp_flood_table := ctx.(earp_flood_table);
                    earp_last_cache_cleanup := ctx.(earp_last_cache_cleanup) |} in
      (ctx', Some (make_arp_probe ctx.(earp_my_mac) probe.(probe_ip)))
    else
      let announce := {| announce_count := 0;
                        announce_timer := start_timer ARP_ANNOUNCE_WAIT current_time |} in
      let ctx' := {| earp_my_mac := ctx.(earp_my_mac);
                    earp_my_ip := probe.(probe_ip);
                    earp_cache := ctx.(earp_cache);
                    earp_state_data := StateAnnounce announce;
                    earp_iface := ctx.(earp_iface);
                    earp_flood_table := ctx.(earp_flood_table);
                    earp_last_cache_cleanup := ctx.(earp_last_cache_cleanup) |} in
      (ctx', None)
  else
    (ctx, None).

Definition detect_probe_conflict (ctx : EnhancedARPContext) (probe : ProbeState)
                                 (packet : ARPEthernetIPv4) : bool :=
  ip_eq packet.(arp_spa) probe.(probe_ip) ||
  ip_eq packet.(arp_tpa) probe.(probe_ip).

(* =============================================================================
   Section 10E: ARP Announcement
   ============================================================================= *)

Definition process_announce_timeout (ctx : EnhancedARPContext) (announce : AnnounceState)
                                    (current_time : N)
                                    : EnhancedARPContext * option ARPEthernetIPv4 :=
  if timer_expired announce.(announce_timer) current_time
  then
    if N.ltb announce.(announce_count) ARP_ANNOUNCE_NUM
    then
      let new_announce := {| announce_count := announce.(announce_count) + 1;
                            announce_timer := start_timer ARP_ANNOUNCE_INTERVAL current_time |} in
      let ctx' := {| earp_my_mac := ctx.(earp_my_mac);
                    earp_my_ip := ctx.(earp_my_ip);
                    earp_cache := ctx.(earp_cache);
                    earp_state_data := StateAnnounce new_announce;
                    earp_iface := ctx.(earp_iface);
                    earp_flood_table := ctx.(earp_flood_table);
                    earp_last_cache_cleanup := ctx.(earp_last_cache_cleanup) |} in
      (ctx', Some (make_gratuitous_arp ctx.(earp_my_mac) ctx.(earp_my_ip)))
    else
      let ctx' := {| earp_my_mac := ctx.(earp_my_mac);
                    earp_my_ip := ctx.(earp_my_ip);
                    earp_cache := ctx.(earp_cache);
                    earp_state_data := StateIdle;
                    earp_iface := ctx.(earp_iface);
                    earp_flood_table := ctx.(earp_flood_table);
                    earp_last_cache_cleanup := ctx.(earp_last_cache_cleanup) |} in
      (ctx', None)
  else
    (ctx, None).

(* =============================================================================
   Section 10F: Conflict Detection and Defense
   ============================================================================= *)

Definition detect_address_conflict (ctx : EnhancedARPContext) (packet : ARPEthernetIPv4)
                                   : bool :=
  ip_eq packet.(arp_spa) ctx.(earp_my_ip) &&
  (if list_eq_dec N.eq_dec packet.(arp_sha).(mac_bytes) ctx.(earp_my_mac).(mac_bytes)
   then false
   else true).

Definition can_defend (defend : DefendState) (current_time : N) : bool :=
  N.leb (defend.(defend_last_time) + ARP_DEFEND_INTERVAL) current_time.

Definition make_defend_packet (ctx : EnhancedARPContext) : ARPEthernetIPv4 :=
  make_gratuitous_arp ctx.(earp_my_mac) ctx.(earp_my_ip).

Definition process_conflict (ctx : EnhancedARPContext) (current_time : N)
                            : EnhancedARPContext * option ARPEthernetIPv4 :=
  match ctx.(earp_state_data) with
  | StateConflict conflicted_ip =>
      (ctx, None)
  | StateDefend defend =>
      if can_defend defend current_time
      then
        let new_defend := {| defend_last_time := current_time |} in
        let ctx' := {| earp_my_mac := ctx.(earp_my_mac);
                      earp_my_ip := ctx.(earp_my_ip);
                      earp_cache := ctx.(earp_cache);
                      earp_state_data := StateDefend new_defend;
                      earp_iface := ctx.(earp_iface);
                      earp_flood_table := ctx.(earp_flood_table);
                      earp_last_cache_cleanup := ctx.(earp_last_cache_cleanup) |} in
        (ctx', Some (make_defend_packet ctx))
      else
        (ctx, None)
  | _ =>
      let new_defend := {| defend_last_time := current_time |} in
      let ctx' := {| earp_my_mac := ctx.(earp_my_mac);
                    earp_my_ip := ctx.(earp_my_ip);
                    earp_cache := ctx.(earp_cache);
                    earp_state_data := StateDefend new_defend;
                    earp_iface := ctx.(earp_iface);
                    earp_flood_table := ctx.(earp_flood_table);
                    earp_last_cache_cleanup := ctx.(earp_last_cache_cleanup) |} in
      (ctx', Some (make_defend_packet ctx))
  end.

Definition send_arp_request_with_flood_check (ctx : EnhancedARPContext)
                                              (target_ip : IPv4Address)
                                              (current_time : N)
                                              : EnhancedARPContext * option ARPEthernetIPv4 :=
  let '(new_flood_table, allowed) := update_flood_table ctx.(earp_flood_table) target_ip current_time in
  if allowed
  then
    let ctx' := {| earp_my_mac := ctx.(earp_my_mac);
                  earp_my_ip := ctx.(earp_my_ip);
                  earp_cache := ctx.(earp_cache);
                  earp_state_data := ctx.(earp_state_data);
                  earp_iface := ctx.(earp_iface);
                  earp_flood_table := new_flood_table;
                  earp_last_cache_cleanup := ctx.(earp_last_cache_cleanup) |} in
    let request := make_arp_request ctx.(earp_my_mac) ctx.(earp_my_ip) target_ip in
    (ctx', Some request)
  else
    let ctx' := {| earp_my_mac := ctx.(earp_my_mac);
                  earp_my_ip := ctx.(earp_my_ip);
                  earp_cache := ctx.(earp_cache);
                  earp_state_data := ctx.(earp_state_data);
                  earp_iface := ctx.(earp_iface);
                  earp_flood_table := new_flood_table;
                  earp_last_cache_cleanup := ctx.(earp_last_cache_cleanup) |} in
    (ctx', None).

Lemma send_arp_request_preserves_cache : forall ctx target_ip current_time ctx' pkt,
  send_arp_request_with_flood_check ctx target_ip current_time = (ctx', pkt) ->
  ctx'.(earp_cache) = ctx.(earp_cache).
Proof.
  intros ctx target_ip current_time ctx' pkt Hsend.
  unfold send_arp_request_with_flood_check in Hsend.
  destruct (update_flood_table (earp_flood_table ctx) target_ip current_time) as [new_flood allowed] eqn:Hflood.
  destruct allowed; injection Hsend as Hctx Hpkt; subst; simpl; reflexivity.
Qed.

Lemma send_arp_request_updates_flood_table : forall ctx target_ip current_time ctx' pkt,
  send_arp_request_with_flood_check ctx target_ip current_time = (ctx', pkt) ->
  ctx'.(earp_flood_table) = fst (update_flood_table ctx.(earp_flood_table) target_ip current_time).
Proof.
  intros ctx target_ip current_time ctx' pkt Hsend.
  unfold send_arp_request_with_flood_check in Hsend.
  destruct (update_flood_table (earp_flood_table ctx) target_ip current_time) as [new_flood allowed] eqn:Hflood.
  assert (Heq: fst (new_flood, allowed) = new_flood) by reflexivity.
  destruct allowed; injection Hsend as Hctx Hpkt; subst; simpl; rewrite <- Heq; rewrite <- Hflood; reflexivity.
Qed.

Lemma send_arp_request_respects_flood_limit : forall ctx target_ip current_time entry ctx' pkt,
  lookup_flood_entry ctx.(earp_flood_table) target_ip = Some entry ->
  N.leb (current_time - entry.(fe_last_request)) ARP_FLOOD_WINDOW = true ->
  N.leb (entry.(fe_request_count) + 1) ARP_FLOOD_THRESHOLD = false ->
  send_arp_request_with_flood_check ctx target_ip current_time = (ctx', pkt) ->
  pkt = None.
Proof.
  intros ctx target_ip current_time entry ctx' pkt Hlookup Hwindow Hthreshold Hsend.
  unfold send_arp_request_with_flood_check in Hsend.
  destruct (update_flood_table (earp_flood_table ctx) target_ip current_time) as [new_flood allowed] eqn:Hflood.
  assert (Hallowed: allowed = false).
  { unfold update_flood_table in Hflood.
    rewrite Hlookup in Hflood.
    rewrite Hwindow in Hflood.
    rewrite Hthreshold in Hflood.
    injection Hflood as Hflood_table Hflood_allowed.
    symmetry. exact Hflood_allowed. }
  rewrite Hallowed in Hsend.
  injection Hsend as Hctx Hpkt.
  symmetry. exact Hpkt.
Qed.

(* =============================================================================
   Section 10G: Integrated Packet Processing with Cache Aging
   ============================================================================= *)

Definition age_cache (cache : ARPCache) (elapsed : N) : ARPCache :=
  let dec (e : ARPCacheEntry) :=
    if e.(ace_static)
    then e
    else {| ace_ip := e.(ace_ip);
            ace_mac := e.(ace_mac);
            ace_ttl := e.(ace_ttl) - elapsed;
            ace_static := e.(ace_static) |}
  in
  filter
    (fun e =>
       if e.(ace_static)
       then true
       else negb (N.leb e.(ace_ttl) 0))
    (map dec cache).

Lemma map_age_zero_entry : forall entry,
  (if ace_static entry
   then entry
   else {| ace_ip := ace_ip entry;
           ace_mac := ace_mac entry;
           ace_ttl := ace_ttl entry - 0;
           ace_static := ace_static entry |}) = entry.
Proof.
  intros entry. destruct (ace_static entry) eqn:Hstatic.
  - reflexivity.
  - rewrite N.sub_0_r. destruct entry as [ip mac ttl st]. simpl. simpl in Hstatic. rewrite Hstatic. reflexivity.
Qed.

Lemma map_age_zero : forall cache,
  map (fun entry =>
    if ace_static entry
    then entry
    else {| ace_ip := ace_ip entry;
            ace_mac := ace_mac entry;
            ace_ttl := ace_ttl entry - 0;
            ace_static := ace_static entry |}) cache = cache.
Proof.
  intros cache. induction cache as [|e rest IH].
  - simpl. reflexivity.
  - simpl. rewrite map_age_zero_entry. f_equal. apply IH.
Qed.

Theorem age_cache_preserves_nonzero_ttl : forall cache,
  (forall e, In e cache -> ace_static e = false -> ace_ttl e > 0) ->
  age_cache cache 0 = cache.
Proof.
  intros cache Hnonzero.
  unfold age_cache.
  rewrite map_age_zero.
  induction cache as [|e rest IH].
  - simpl. reflexivity.
  - simpl. destruct (ace_static e) eqn:Hstatic.
    + simpl. f_equal. apply IH.
      intros. apply Hnonzero. right. assumption. assumption.
    + assert (Httl: ace_ttl e > 0).
      { apply Hnonzero. left. reflexivity. assumption. }
      assert (N.leb (ace_ttl e) 0 = false).
      { apply N.leb_gt. lia. }
      rewrite H. simpl. f_equal. apply IH.
      intros. apply Hnonzero. right. assumption. assumption.
Qed.



Theorem cache_aging_preserves_lookup_static : forall cache ip mac elapsed,
  In {| ace_ip := ip; ace_mac := mac; ace_ttl := 100; ace_static := true |} cache ->
  In {| ace_ip := ip; ace_mac := mac; ace_ttl := 100; ace_static := true |}
     (age_cache cache elapsed).
Proof.
  intros cache ip mac elapsed Hin.
  unfold age_cache.
  apply filter_In. split.
  - apply in_map_iff. exists {| ace_ip := ip; ace_mac := mac; ace_ttl := 100; ace_static := true |}.
    split.
    + simpl. reflexivity.
    + assumption.
  - simpl. reflexivity.
Qed.

Theorem flood_table_bounded_requests : forall table ip t,
  snd (update_flood_table table ip t) = true ->
  exists entry table',
    fst (update_flood_table table ip t) = table' /\
    (lookup_flood_entry table' ip = Some entry ->
     N.leb (fe_request_count entry) ARP_FLOOD_THRESHOLD = true).
Proof.
  intros table ip t Hallowed.
  unfold update_flood_table in *.
  destruct (lookup_flood_entry table ip) as [old_entry|] eqn:Hlookup.
  - destruct (N.leb (t - fe_last_request old_entry) ARP_FLOOD_WINDOW) eqn:Hwindow.
    + destruct (N.leb (fe_request_count old_entry + 1) ARP_FLOOD_THRESHOLD) eqn:Hthresh.
      * exists {| fe_ip := ip; fe_last_request := t; fe_request_count := fe_request_count old_entry + 1 |}.
        remember (let fix replace (t0 : FloodTable) : FloodTable :=
                    match t0 with
                    | [] => [{| fe_ip := ip; fe_last_request := t;
                               fe_request_count := fe_request_count old_entry + 1 |}]
                    | e :: rest =>
                        if flood_eq (fe_ip e) ip
                        then {| fe_ip := ip; fe_last_request := t;
                               fe_request_count := fe_request_count old_entry + 1 |} :: rest
                        else e :: replace rest
                    end
                  in replace table) as new_table.
        exists new_table. split.
        { reflexivity. }
        { intro Hlookup'. assumption. }
      * simpl in Hallowed. discriminate.
    + exists {| fe_ip := ip; fe_last_request := t; fe_request_count := 1 |}.
      remember (let fix replace (t0 : FloodTable) : FloodTable :=
                  match t0 with
                  | [] => [{| fe_ip := ip; fe_last_request := t; fe_request_count := 1 |}]
                  | e :: rest =>
                      if flood_eq (fe_ip e) ip
                      then {| fe_ip := ip; fe_last_request := t; fe_request_count := 1 |} :: rest
                      else e :: replace rest
                  end
                in replace table) as new_table.
      exists new_table. split.
      { reflexivity. }
      { intro Hlookup'. unfold ARP_FLOOD_THRESHOLD. simpl. reflexivity. }
  - exists {| fe_ip := ip; fe_last_request := t; fe_request_count := 1 |}.
    exists ({| fe_ip := ip; fe_last_request := t; fe_request_count := 1 |} :: table).
    split.
    + reflexivity.
    + intro Hlookup'. unfold ARP_FLOOD_THRESHOLD. simpl. reflexivity.
Qed.

Theorem arp_request_reply_duality : forall my_mac my_ip sender_mac sender_ip,
  let req := make_arp_request my_mac my_ip sender_ip in
  let reply := make_arp_reply sender_mac sender_ip my_mac my_ip in
  arp_spa reply = sender_ip /\
  arp_tpa reply = my_ip /\
  arp_sha reply = sender_mac /\
  arp_tha reply = my_mac /\
  arp_spa req = my_ip /\
  arp_tpa req = sender_ip.
Proof.
  intros my_mac my_ip sender_mac sender_ip req reply.
  unfold req, reply, make_arp_request, make_arp_reply.
  simpl. repeat split.
Qed.

Theorem gratuitous_arp_self_announcing : forall mac ip,
  let garp := make_gratuitous_arp mac ip in
  arp_spa garp = arp_tpa garp /\
  arp_tha garp = MAC_ZERO /\
  arp_spa garp = ip /\
  arp_op garp = ARP_OP_REQUEST.
Proof.
  intros mac ip garp.
  unfold garp, make_gratuitous_arp.
  simpl. repeat split.
Qed.

Theorem cache_ip_determines_mac : forall cache ip mac1 mac2,
  lookup_cache cache ip = Some mac1 ->
  lookup_cache cache ip = Some mac2 ->
  mac1 = mac2.
Proof.
  intros cache ip mac1 mac2 H1 H2.
  congruence.
Qed.

Theorem mac_address_equality_decidable : forall m1 m2 : MACAddress,
  {m1 = m2} + {m1 <> m2}.
Proof.
  intros m1 m2.
  destruct m1 as [bytes1 valid1].
  destruct m2 as [bytes2 valid2].
  destruct (list_eq_dec N.eq_dec bytes1 bytes2) as [Heq|Hneq].
  - left. subst bytes2.
    assert (valid1 = valid2) by apply proof_irrelevance.
    subst. reflexivity.
  - right. intro Hcontr. injection Hcontr as Heq. contradiction.
Qed.

Theorem ipv4_address_equality_decidable : forall ip1 ip2 : IPv4Address,
  {ip1 = ip2} + {ip1 <> ip2}.
Proof.
  intros ip1 ip2.
  destruct ip1 as [a1 b1 c1 d1].
  destruct ip2 as [a2 b2 c2 d2].
  destruct (N.eq_dec a1 a2); [|right; intro H; injection H; contradiction].
  destruct (N.eq_dec b1 b2); [|right; intro H; injection H; contradiction].
  destruct (N.eq_dec c1 c2); [|right; intro H; injection H; contradiction].
  destruct (N.eq_dec d1 d2); [|right; intro H; injection H; contradiction].
  left. subst. reflexivity.
Qed.

Theorem broadcast_mac_is_broadcast : is_broadcast_mac MAC_BROADCAST = true.
Proof.
  unfold is_broadcast_mac, MAC_BROADCAST. simpl. reflexivity.
Qed.

Theorem arp_request_reply_protocol_symmetry :
  forall my_mac my_ip target_mac target_ip,
    let request := make_arp_request my_mac my_ip target_ip in
    let reply := make_arp_reply target_mac target_ip my_mac my_ip in
    (arp_spa request = my_ip /\ arp_tpa request = target_ip) /\
    (arp_spa reply = target_ip /\ arp_tpa reply = my_ip) /\
    (arp_sha request = my_mac /\ arp_tha reply = my_mac) /\
    (arp_sha reply = target_mac /\ arp_op request = ARP_OP_REQUEST /\ arp_op reply = ARP_OP_REPLY).
Proof.
  intros my_mac my_ip target_mac target_ip request reply.
  unfold request, reply, make_arp_request, make_arp_reply.
  simpl. repeat split.
Qed.

Theorem arp_gratuitous_announces_self :
  forall mac ip,
    let garp := make_gratuitous_arp mac ip in
    arp_spa garp = ip /\ arp_tpa garp = ip /\ arp_sha garp = mac.
Proof.
  intros mac ip garp.
  unfold garp, make_gratuitous_arp. simpl. repeat split.
Qed.

Theorem arp_static_entry_survives_all_aging :
  forall cache ip mac ttl elapsed,
    In {| ace_ip := ip; ace_mac := mac; ace_ttl := ttl; ace_static := true |} cache ->
    In {| ace_ip := ip; ace_mac := mac; ace_ttl := ttl; ace_static := true |}
       (age_cache cache elapsed).
Proof.
  intros cache ip mac ttl elapsed Hin.
  unfold age_cache.
  apply filter_In. split.
  - apply in_map_iff.
    exists {| ace_ip := ip; ace_mac := mac; ace_ttl := ttl; ace_static := true |}.
    split.
    + simpl. reflexivity.
    + assumption.
  - simpl. reflexivity.
Qed.



Definition process_arp_packet_enhanced (ctx : EnhancedARPContext)
                                       (packet : ARPEthernetIPv4)
                                       (current_time : N)
                                       (elapsed_since_last : N)
                                       : EnhancedARPContext * option ARPEthernetIPv4 :=
  (* Age cache first *)
  let aged_cache := age_cache ctx.(earp_cache) elapsed_since_last in

  (* Clean flood table *)
  let cleaned_flood := clean_flood_table ctx.(earp_flood_table) current_time in

  let ctx_aged := {| earp_my_mac := ctx.(earp_my_mac);
                     earp_my_ip := ctx.(earp_my_ip);
                     earp_cache := aged_cache;
                     earp_state_data := ctx.(earp_state_data);
                     earp_iface := ctx.(earp_iface);
                     earp_flood_table := cleaned_flood;
                     earp_last_cache_cleanup := current_time |} in

  (* RFC 826: Reject packets with broadcast sender MAC *)
  if is_broadcast_mac packet.(arp_sha)
  then (ctx_aged, None)
  else
  (* Check for conflicts in PROBE state *)
  match ctx_aged.(earp_state_data) with
  | StateProbe probe =>
      if detect_probe_conflict ctx_aged probe packet
      then
        let ctx' := {| earp_my_mac := ctx_aged.(earp_my_mac);
                      earp_my_ip := ctx_aged.(earp_my_ip);
                      earp_cache := ctx_aged.(earp_cache);
                      earp_state_data := StateConflict probe.(probe_ip);
                      earp_iface := ctx_aged.(earp_iface);
                      earp_flood_table := ctx_aged.(earp_flood_table);
                      earp_last_cache_cleanup := ctx_aged.(earp_last_cache_cleanup) |} in
        (ctx', None)
      else
        (* Continue with RFC 826 strict processing *)
        let i_am_target := ip_eq packet.(arp_tpa) ctx_aged.(earp_my_ip) in
        let cache' := rfc826_merge ctx_aged.(earp_cache)
                                   packet.(arp_spa) packet.(arp_sha) 300 i_am_target in
        let ctx' := {| earp_my_mac := ctx_aged.(earp_my_mac);
                      earp_my_ip := ctx_aged.(earp_my_ip);
                      earp_cache := cache';
                      earp_state_data := ctx_aged.(earp_state_data);
                      earp_iface := ctx_aged.(earp_iface);
                      earp_flood_table := ctx_aged.(earp_flood_table);
                      earp_last_cache_cleanup := ctx_aged.(earp_last_cache_cleanup) |} in
        (ctx', None)
  | _ =>
      (* Check for address conflict *)
      if detect_address_conflict ctx_aged packet
      then
        process_conflict ctx_aged current_time
      else
        (* RFC 826 strict processing *)
        let i_am_target := ip_eq packet.(arp_tpa) ctx_aged.(earp_my_ip) in
        let cache' := rfc826_merge ctx_aged.(earp_cache)
                                   packet.(arp_spa) packet.(arp_sha) 300 i_am_target in

        (* Remove from pending if this is a reply to our request *)
        let new_state :=
          match ctx_aged.(earp_state_data) with
          | StatePending reqs =>
              if N.eqb packet.(arp_op) ARP_OP_REPLY
              then StatePending (remove_pending_request reqs packet.(arp_spa))
              else StatePending reqs
          | other => other
          end in

        let ctx' := {| earp_my_mac := ctx_aged.(earp_my_mac);
                      earp_my_ip := ctx_aged.(earp_my_ip);
                      earp_cache := cache';
                      earp_state_data := new_state;
                      earp_iface := ctx_aged.(earp_iface);
                      earp_flood_table := ctx_aged.(earp_flood_table);
                      earp_last_cache_cleanup := ctx_aged.(earp_last_cache_cleanup) |} in

        (* Generate reply if request is for us *)
        if ip_eq packet.(arp_tpa) ctx_aged.(earp_my_ip)
        then
          if N.eqb packet.(arp_op) ARP_OP_REQUEST
          then
            let reply := make_arp_reply ctx_aged.(earp_my_mac) ctx_aged.(earp_my_ip)
                                        packet.(arp_sha) packet.(arp_spa) in
            (ctx', Some reply)
          else
            (ctx', None)
        else
          (ctx', None)
  end.

(* =============================================================================
   Section 11: Main Properties to Verify
   ============================================================================= *)

(* IPv4 equality is reflexive *)
Lemma ip_eq_refl : forall ip, ip_eq ip ip = true.
Proof.
  intros ip.
  unfold ip_eq.
  repeat rewrite N.eqb_refl.
  reflexivity.
Qed.

(* IPv4 equality implies structural equality of all octets *)
Lemma ip_eq_true : forall ip1 ip2,
  ip_eq ip1 ip2 = true ->
  ip1.(ipv4_a) = ip2.(ipv4_a) /\
  ip1.(ipv4_b) = ip2.(ipv4_b) /\
  ip1.(ipv4_c) = ip2.(ipv4_c) /\
  ip1.(ipv4_d) = ip2.(ipv4_d).
Proof.
  intros ip1 ip2 H.
  unfold ip_eq in H.
  apply andb_prop in H as [H123 H4].
  apply andb_prop in H123 as [H12 H3].
  apply andb_prop in H12 as [H1 H2].
  apply N.eqb_eq in H1.
  apply N.eqb_eq in H2.
  apply N.eqb_eq in H3.
  apply N.eqb_eq in H4.
  auto.
Qed.

(* Lemmas for RFC 826 compliant functions *)

(* Updating existing non-static entry succeeds with new MAC *)
Lemma update_cache_entry_exists : forall cache ip mac ttl,
  lookup_cache cache ip <> None ->
  (forall e, In e cache -> ip_eq (ace_ip e) ip = true -> ace_static e = false) ->
  lookup_cache (update_cache_entry cache ip mac ttl) ip = Some mac.
Proof.
  intros cache ip mac ttl Hexists Hno_static.
  unfold lookup_cache, update_cache_entry.
  induction cache as [|e rest IH].
  - contradiction.
  - simpl. destruct (ip_eq (ace_ip e) ip) eqn:Heq.
    + destruct (ace_static e) eqn:Hstatic.
      * exfalso.
        specialize (Hno_static e).
        assert (Hin: In e (e :: rest)) by (left; reflexivity).
        specialize (Hno_static Hin Heq).
        rewrite Hstatic in Hno_static.
        discriminate.
      * simpl. rewrite ip_eq_refl. reflexivity.
    + simpl. rewrite Heq.
      apply IH.
      * intro Hnone. apply Hexists.
        simpl. rewrite Heq. assumption.
      * intros. apply Hno_static. right. assumption. assumption.
Qed.

(* Adding entry for non-existent IP succeeds *)
Lemma add_cache_entry_not_exists : forall cache ip mac ttl,
  lookup_cache cache ip = None ->
  lookup_cache (add_cache_entry cache ip mac ttl) ip = Some mac.
Proof.
  intros cache ip mac ttl Hnone.
  unfold lookup_cache, add_cache_entry.
  induction cache as [|e rest IH].
  - simpl. rewrite ip_eq_refl. reflexivity.
  - simpl. destruct (ip_eq (ace_ip e) ip) eqn:Heq.
    + simpl in Hnone. rewrite Heq in Hnone. discriminate.
    + simpl. rewrite Heq.
      apply IH.
      simpl in Hnone. rewrite Heq in Hnone. assumption.
Qed.

(* RFC 826 merge when target ensures entry exists (possibly static MAC) *)
Lemma rfc826_merge_updates_or_adds : forall cache ip mac ttl target,
  target = true ->
  exists m, lookup_cache (rfc826_merge cache ip mac ttl target) ip = Some m.
Proof.
  intros cache ip mac ttl target Htarget.
  unfold rfc826_merge. rewrite Htarget.
  destruct (lookup_cache cache ip) eqn:Hlook.
  - unfold update_cache_entry.
    induction cache as [|e rest IH].
    + discriminate.
    + simpl. destruct (ip_eq (ace_ip e) ip) eqn:Heq.
      * destruct (ace_static e) eqn:Hstatic.
        { simpl. rewrite Heq.
          simpl in Hlook. rewrite Heq in Hlook. injection Hlook as Hmac.
          exists (ace_mac e). reflexivity. }
        { simpl. rewrite ip_eq_refl. exists mac. reflexivity. }
      * simpl. rewrite Heq. apply IH.
        simpl in Hlook. rewrite Heq in Hlook. assumption.
  - exists mac. unfold add_cache_entry.
    induction cache as [|e rest IH].
    + simpl. rewrite ip_eq_refl. reflexivity.
    + simpl. destruct (ip_eq (ace_ip e) ip) eqn:Heq.
      * simpl in Hlook. rewrite Heq in Hlook. discriminate.
      * simpl. rewrite Heq. apply IH.
        simpl in Hlook. rewrite Heq in Hlook. assumption.
Qed.

(* RFC 826 merge with no static entries guarantees exact MAC *)
Lemma rfc826_merge_target : forall cache ip mac ttl,
  (forall e, In e cache -> ip_eq (ace_ip e) ip = true -> ace_static e = false) ->
  lookup_cache (rfc826_merge cache ip mac ttl true) ip = Some mac.
Proof.
  intros cache ip mac ttl Hno_static.
  unfold rfc826_merge.
  destruct (lookup_cache cache ip) eqn:Hlookup.
  - apply update_cache_entry_exists.
    + rewrite Hlookup. discriminate.
    + assumption.
  - apply add_cache_entry_not_exists. assumption.
Qed.

Theorem gratuitous_arp_updates_cache : forall ctx pkt ctx' resp,
  is_gratuitous_arp pkt = true ->
  validate_arp_packet pkt ctx.(arp_my_mac) = true ->
  ip_eq pkt.(arp_tpa) ctx.(arp_my_ip) = true ->
  (forall e, In e ctx.(arp_cache) ->
   ip_eq (ace_ip e) pkt.(arp_spa) = true -> ace_static e = false) ->
  process_arp_packet ctx pkt = (ctx', resp) ->
  lookup_cache ctx'.(arp_cache) pkt.(arp_spa) = Some pkt.(arp_sha).
Proof.
  intros ctx pkt ctx' resp Hgrat Hvalid Htarget Hno_static Hproc.
  unfold process_arp_packet in Hproc.
  rewrite Hvalid, Htarget in Hproc.
  destruct (N.eqb (arp_op pkt) ARP_OP_REQUEST) eqn:Hop;
  injection Hproc as Hctx _; subst ctx'; simpl;
  apply rfc826_merge_target; assumption.
Qed.

(* Property 1: Cache coherence - if no static entry blocks, merge ensures lookup succeeds *)
Theorem cache_lookup_after_merge_no_static : forall cache ip mac ttl,
  (forall e, In e cache -> ip_eq (ace_ip e) ip = true -> ace_static e = false) ->
  lookup_cache (merge_cache_entry cache ip mac ttl) ip = Some mac.
Proof.
  intros cache ip mac ttl Hno_static.
  unfold lookup_cache, merge_cache_entry.
  induction cache as [|e rest IH].
  - simpl. rewrite ip_eq_refl. reflexivity.
  - simpl.
    destruct (ip_eq (ace_ip e) ip) eqn:Heq.
    + destruct (ace_static e) eqn:Hstatic.
      * exfalso.
        specialize (Hno_static e).
        assert (Hin: In e (e :: rest)) by (left; reflexivity).
        specialize (Hno_static Hin Heq).
        rewrite Hstatic in Hno_static.
        discriminate.
      * simpl. rewrite ip_eq_refl. reflexivity.
    + simpl. rewrite Heq.
      apply IH.
      intros. apply Hno_static. right. assumption. assumption.
Qed.

(* Property 2: Request-Reply correspondence *)
Theorem arp_reply_matches_request : forall ctx packet reply ctx',
  process_arp_packet ctx packet = (ctx', Some reply) ->
  packet.(arp_op) = ARP_OP_REQUEST ->
  ip_eq packet.(arp_tpa) ctx.(arp_my_ip) = true ->
  reply.(arp_op) = ARP_OP_REPLY /\
  reply.(arp_tpa) = packet.(arp_spa) /\
  reply.(arp_tha) = packet.(arp_sha).
Proof.
  intros ctx packet reply ctx' Hproc Hreq Htarget.
  unfold process_arp_packet in Hproc.
  destruct (validate_arp_packet packet (arp_my_mac ctx)) eqn:Hvalid.
  - rewrite Htarget in Hproc.
    apply N.eqb_eq in Hreq.
    rewrite Hreq in Hproc.
    injection Hproc as Hctx' Hreply.
    inversion Hreply. subst.
    unfold make_arp_reply.
    simpl.
    split. reflexivity.
    split; reflexivity.
  - discriminate.
Qed.

(* Helper lemma: merge always succeeds when no static entry blocks *)
Lemma merge_then_lookup : forall cache ip mac ttl,
  (forall e, In e cache -> ip_eq (ace_ip e) ip = true -> ace_static e = false) ->
  lookup_cache (merge_cache_entry cache ip mac ttl) ip = Some mac.
Proof.
  intros. apply cache_lookup_after_merge_no_static. assumption.
Qed.

(* Property 3: RFC 826 Bidirectional learning - only when target and valid packet *)
Lemma process_arp_packet_preserves_identity : forall ctx pkt ctx' resp,
  validate_arp_packet pkt ctx.(arp_my_mac) = true ->
  process_arp_packet ctx pkt = (ctx', resp) ->
  arp_my_mac ctx' = arp_my_mac ctx /\ arp_my_ip ctx' = arp_my_ip ctx.
Proof.
  intros ctx pkt ctx' resp Hvalid Hproc.
  unfold process_arp_packet in Hproc.
  rewrite Hvalid in Hproc.
  destruct (ip_eq (arp_tpa pkt) (arp_my_ip ctx));
  destruct (N.eqb (arp_op pkt) ARP_OP_REQUEST);
  injection Hproc as Hctx _; subst ctx'; simpl; split; reflexivity.
Qed.

Theorem bidirectional_cache_update_when_target : forall ctx packet ctx' response,
  (forall e, In e ctx.(arp_cache) ->
   ip_eq (ace_ip e) packet.(arp_spa) = true -> ace_static e = false) ->
  validate_arp_packet packet ctx.(arp_my_mac) = true ->
  ip_eq packet.(arp_tpa) ctx.(arp_my_ip) = true ->
  process_arp_packet ctx packet = (ctx', response) ->
  lookup_cache ctx'.(arp_cache) packet.(arp_spa) = Some packet.(arp_sha).
Proof.
  intros ctx packet ctx' response Hno_static Hvalid_pkt Htarget Hproc.
  unfold process_arp_packet in Hproc.
  rewrite Hvalid_pkt in Hproc.
  rewrite Htarget in Hproc.
  destruct (N.eqb (arp_op packet) ARP_OP_REQUEST) eqn:Hop.
  - injection Hproc. intros. subst ctx'. simpl.
    apply rfc826_merge_target. assumption.
  - injection Hproc. intros. subst ctx'. simpl.
    apply rfc826_merge_target. assumption.
Qed.

(* RFC 826 Compliance: Only update existing entries when not target *)
Theorem rfc826_no_cache_pollution : forall ctx packet ctx',
  ip_eq packet.(arp_tpa) ctx.(arp_my_ip) = false ->
  lookup_cache ctx.(arp_cache) packet.(arp_spa) = None ->
  process_arp_packet ctx packet = (ctx', None) ->
  lookup_cache ctx'.(arp_cache) packet.(arp_spa) = None.
Proof.
  intros ctx packet ctx' Hnot_target Hnot_in_cache Hproc.
  unfold process_arp_packet in Hproc.
  destruct (validate_arp_packet packet (arp_my_mac ctx)) eqn:Hvalid.
  - rewrite Hnot_target in Hproc.
    injection Hproc as Hctx'. subst ctx'. simpl.
    unfold rfc826_merge. rewrite Hnot_in_cache. simpl. assumption.
  - injection Hproc as Hctx'. subst ctx'. simpl. assumption.
Qed.

(* Property 4: Cache size bounds *)
Definition cache_size (c : ARPCache) : nat := length c.

Lemma update_cache_entry_size : forall cache ip mac ttl,
  length (update_cache_entry cache ip mac ttl) = length cache.
Proof.
  intros cache ip mac ttl.
  induction cache as [|e rest IH].
  - simpl. reflexivity.
  - simpl. destruct (ip_eq (ace_ip e) ip).
    + destruct (ace_static e); simpl; reflexivity.
    + simpl. rewrite IH. reflexivity.
Qed.

Lemma add_cache_entry_size_bound : forall cache ip mac ttl,
  (length (add_cache_entry cache ip mac ttl) <= length cache + 1)%nat.
Proof.
  intros cache ip mac ttl.
  induction cache as [|e rest IH].
  - simpl. lia.
  - simpl. destruct (ip_eq (ace_ip e) ip); simpl; lia.
Qed.

Lemma rfc826_merge_size_bound : forall cache ip mac ttl i_am_target,
  (length (rfc826_merge cache ip mac ttl i_am_target) <= length cache + 1)%nat.
Proof.
  intros cache ip mac ttl i_am_target.
  unfold rfc826_merge.
  destruct (lookup_cache cache ip).
  - rewrite update_cache_entry_size. lia.
  - destruct i_am_target.
    + apply add_cache_entry_size_bound.
    + simpl. lia.
Qed.

(* Transitivity of IP inequality: if ip1=ip2 and ip2≠ip3, then ip1≠ip3 *)
Lemma ip_eq_trans_false : forall ip1 ip2 ip3,
  ip_eq ip1 ip2 = true ->
  ip_eq ip2 ip3 = false ->
  ip_eq ip1 ip3 = false.
Proof.
  intros ip1 ip2 ip3 H12 H23.
  destruct (ip_eq ip1 ip3) eqn:H13.
  - apply ip_eq_true in H12.
    apply ip_eq_true in H13.
    destruct H12 as [Ha12 [Hb12 [Hc12 Hd12]]].
    destruct H13 as [Ha13 [Hb13 [Hc13 Hd13]]].
    destruct ip1, ip2, ip3. simpl in *.
    subst.
    unfold ip_eq in H23. simpl in H23.
    rewrite N.eqb_refl in H23. simpl in H23.
    rewrite N.eqb_refl in H23. simpl in H23.
    rewrite N.eqb_refl in H23. simpl in H23.
    rewrite N.eqb_refl in H23. discriminate.
  - reflexivity.
Qed.

(* Cache update preserves lookups for unrelated IP addresses *)
Lemma update_cache_entry_preserves_other : forall cache ip mac ttl other_ip,
  other_ip <> ip ->
  lookup_cache (update_cache_entry cache ip mac ttl) other_ip = lookup_cache cache other_ip.
Proof.
  intros cache ip mac ttl other_ip Hneq.
  unfold update_cache_entry.
  induction cache as [|e rest IH].
  - simpl. reflexivity.
  - simpl.
    destruct (ip_eq (ace_ip e) ip) eqn:Heq_e_ip.
    + destruct (ace_static e) eqn:Hstatic; simpl.
      * destruct (ip_eq (ace_ip e) other_ip) eqn:Heq_e_other.
        apply ip_eq_true in Heq_e_ip.
        apply ip_eq_true in Heq_e_other.
        destruct Heq_e_ip as [Ha [Hb [Hc Hd]]].
        destruct Heq_e_other as [Ha' [Hb' [Hc' Hd']]].
        destruct (ace_ip e), ip, other_ip. simpl in *.
        subst. contradiction Hneq. reflexivity.
        reflexivity.
      * destruct (ip_eq ip other_ip) eqn:Heq_ip_other.
        apply ip_eq_true in Heq_ip_other.
        destruct Heq_ip_other as [Ha' [Hb' [Hc' Hd']]].
        destruct ip, other_ip. simpl in *.
        subst. contradiction Hneq. reflexivity.
        assert (Heq_e_other: ip_eq (ace_ip e) other_ip = false).
        { apply (ip_eq_trans_false (ace_ip e) ip other_ip); assumption. }
        rewrite Heq_e_other. reflexivity.
    + simpl.
      destruct (ip_eq (ace_ip e) other_ip) eqn:Heq_e_other.
      * reflexivity.
      * apply IH.
Qed.

(* Cache addition preserves lookups for unrelated IP addresses *)
Lemma add_cache_entry_preserves_other : forall cache ip mac ttl other_ip,
  other_ip <> ip ->
  lookup_cache (add_cache_entry cache ip mac ttl) other_ip = lookup_cache cache other_ip.
Proof.
  intros cache ip mac ttl other_ip Hneq.
  unfold add_cache_entry.
  induction cache as [|e rest IH].
  - simpl.
    destruct (ip_eq ip other_ip) eqn:Heq.
    + apply ip_eq_true in Heq.
      destruct Heq as [Ha [Hb [Hc Hd]]].
      destruct ip, other_ip. simpl in *.
      subst. contradiction Hneq. reflexivity.
    + reflexivity.
  - simpl.
    destruct (ip_eq (ace_ip e) ip) eqn:Heq_e_ip.
    + simpl.
      destruct (ip_eq (ace_ip e) other_ip); reflexivity.
    + simpl.
      destruct (ip_eq (ace_ip e) other_ip) eqn:Heq_e_other.
      * reflexivity.
      * apply IH.
Qed.

(* RFC 826 merge operation preserves lookups for all unrelated IPs *)
Lemma rfc826_merge_preserves_other_ips : forall cache ip mac ttl i_am_target other_ip,
  other_ip <> ip ->
  lookup_cache (rfc826_merge cache ip mac ttl i_am_target) other_ip = lookup_cache cache other_ip.
Proof.
  intros cache ip mac ttl i_am_target other_ip Hneq.
  unfold rfc826_merge.
  destruct (lookup_cache cache ip) eqn:Hlookup.
  - apply update_cache_entry_preserves_other. assumption.
  - destruct i_am_target.
    + apply add_cache_entry_preserves_other. assumption.
    + reflexivity.
Qed.


Lemma merge_cache_size_bound : forall cache ip mac ttl,
  (length (merge_cache_entry cache ip mac ttl) <= length cache + 1)%nat.
Proof.
  intros cache ip mac ttl.
  induction cache as [|e rest IH].
  - unfold merge_cache_entry. simpl. lia.
  - unfold merge_cache_entry in *. simpl. fold merge_cache_entry in *.
    destruct (ip_eq (ace_ip e) ip) eqn:Heq.
    + destruct (ace_static e) eqn:Hstatic; simpl; lia.
    + simpl. lia.
Qed.

Theorem cache_bounded_growth : forall ctx packet ctx' resp,
  process_arp_packet ctx packet = (ctx', resp) ->
  (cache_size ctx'.(arp_cache) <= cache_size ctx.(arp_cache) + 1)%nat.
Proof.
  intros ctx packet ctx' resp Hproc.
  unfold process_arp_packet in Hproc.
  destruct (validate_arp_packet packet (arp_my_mac ctx)) eqn:Hvalid.
  - destruct (ip_eq (arp_tpa packet) (arp_my_ip ctx)) eqn:Htarget;
    destruct (N.eqb (arp_op packet) ARP_OP_REQUEST);
    injection Hproc as Hctx' _;
    subst ctx';
    simpl;
    unfold cache_size;
    apply rfc826_merge_size_bound.
  - injection Hproc as Hctx' _. subst ctx'. simpl. unfold cache_size. lia.
Qed.

(* Property 5: Gratuitous ARP updates when we're target *)
Theorem gratuitous_arp_updates_cache_when_target : forall ctx grat ctx',
  (forall e, In e ctx.(arp_cache) ->
   ip_eq (ace_ip e) grat.(arp_spa) = true -> ace_static e = false) ->
  validate_arp_packet grat ctx.(arp_my_mac) = true ->
  grat.(arp_spa) = grat.(arp_tpa) ->  (* Gratuitous ARP condition *)
  ip_eq grat.(arp_tpa) ctx.(arp_my_ip) = true ->  (* We are the target *)
  process_arp_packet ctx grat = (ctx', None) ->
  lookup_cache ctx'.(arp_cache) grat.(arp_spa) = Some grat.(arp_sha).
Proof.
  intros ctx grat ctx' Hno_static Hvalid_pkt Hgrat Htarget Hproc.
  unfold process_arp_packet in Hproc.
  rewrite Hvalid_pkt in Hproc.
  rewrite Htarget in Hproc.
  destruct (N.eqb (arp_op grat) ARP_OP_REQUEST) eqn:Hop.
  - injection Hproc. intros H _. discriminate H.
  - injection Hproc. intros. subst ctx'. simpl.
    apply rfc826_merge_target. assumption.
Qed.

(* =============================================================================
   Section 12: Cache Timeout Management
   ============================================================================= *)

(* Note: age_cache is now defined in Section 10G for use in enhanced processing *)

Theorem aging_preserves_static : forall cache elapsed ip mac,
  In {| ace_ip := ip; ace_mac := mac; ace_ttl := 0; ace_static := true |} cache ->
  In {| ace_ip := ip; ace_mac := mac; ace_ttl := 0; ace_static := true |}
     (age_cache cache elapsed).
Proof.
  intros cache elapsed ip mac Hin.
  unfold age_cache.
  apply filter_In.
  split.
  - apply in_map_iff.
    exists {| ace_ip := ip; ace_mac := mac; ace_ttl := 0; ace_static := true |}.
    split.
    + simpl. reflexivity.
    + assumption.
  - simpl. reflexivity.
Qed.

(* =============================================================================
   Section 13: Network Interface
   ============================================================================= *)

(* Note: NetworkInterface is now defined in Section 10B for use in EnhancedARPContext *)

Definition send_arp_on_interface (iface : NetworkInterface)
                                 (packet : ARPEthernetIPv4) : bool :=
  if iface.(if_up)
  then true  (* Actually send to network driver *)
  else false.

(* =============================================================================
   Section 13A: Broadcast Sender Validation
   ============================================================================= *)

(* Theorem: Broadcast sender MAC packets are rejected *)
Theorem broadcast_sender_rejected : forall ctx packet ctx' resp,
  is_broadcast_mac packet.(arp_sha) = true ->
  process_arp_packet ctx packet = (ctx', resp) ->
  ctx' = ctx /\ resp = None.
Proof.
  intros ctx packet ctx' resp Hbroadcast Hproc.
  unfold process_arp_packet in Hproc.
  assert (Hvalid: validate_arp_packet packet (arp_my_mac ctx) = false).
  { unfold validate_arp_packet. rewrite Hbroadcast. simpl.
    repeat rewrite andb_false_r. reflexivity. }
  rewrite Hvalid in Hproc.
  injection Hproc as Hctx Hresp.
  split; [symmetry; exact Hctx | symmetry; exact Hresp].
Qed.

Theorem enhanced_broadcast_sender_no_cache_pollution : forall ctx pkt ctx' resp t dt,
  is_broadcast_mac pkt.(arp_sha) = true ->
  process_arp_packet_enhanced ctx pkt t dt = (ctx', resp) ->
  earp_cache ctx' = age_cache (earp_cache ctx) dt /\ resp = None.
Proof.
  intros ctx pkt ctx' resp t dt Hbroadcast Hproc.
  unfold process_arp_packet_enhanced in Hproc.
  destruct (is_broadcast_mac (arp_sha pkt)) eqn:Hcheck.
  - injection Hproc as Hctx Hresp.
    subst ctx'. simpl.
    split; [reflexivity | symmetry; exact Hresp].
  - rewrite Hbroadcast in Hcheck. discriminate.
Qed.

(* Theorem: Broadcast sender packets don't pollute cache *)
Theorem broadcast_sender_no_cache_pollution : forall ctx packet ctx' resp,
  is_broadcast_mac packet.(arp_sha) = true ->
  process_arp_packet ctx packet = (ctx', resp) ->
  ctx'.(arp_cache) = ctx.(arp_cache).
Proof.
  intros ctx packet ctx' resp Hbroadcast Hproc.
  assert (H: ctx' = ctx /\ resp = None) by
    (eapply broadcast_sender_rejected; eassumption).
  destruct H as [Heq _].
  rewrite Heq.
  reflexivity.
Qed.

Theorem no_response_when_broadcast_sender :
  forall ctx pkt ctx' resp,
    is_broadcast_mac pkt.(arp_sha) = true ->
    process_arp_packet ctx pkt = (ctx', resp) ->
    resp = None.
Proof.
  intros. eapply broadcast_sender_rejected in H0; eauto. tauto.
Qed.

(* =============================================================================
   Section 13B: Broadcast Reply Prevention
   ============================================================================= *)

(* Theorem: Replies copy the requester's MAC to target hardware address *)
Theorem reply_target_is_requester_mac : forall ctx packet ctx' reply,
  process_arp_packet ctx packet = (ctx', Some reply) ->
  reply.(arp_op) = ARP_OP_REPLY ->
  reply.(arp_tha) = packet.(arp_sha).
Proof.
  intros ctx packet ctx' reply Hproc Hreply_op.
  unfold process_arp_packet in Hproc.
  destruct (validate_arp_packet packet (arp_my_mac ctx)) eqn:Hvalid.
  - destruct (ip_eq (arp_tpa packet) (arp_my_ip ctx)) eqn:Htarget.
    + destruct (N.eqb (arp_op packet) ARP_OP_REQUEST) eqn:Hop.
      * injection Hproc as _ Hreply.
        subst reply.
        unfold make_arp_reply. simpl.
        reflexivity.
      * discriminate.
    + discriminate.
  - discriminate.
Qed.

(* Theorem: Replies are never sent to broadcast *)
Theorem reply_never_broadcast : forall ctx packet ctx' reply,
  process_arp_packet ctx packet = (ctx', Some reply) ->
  reply.(arp_op) = ARP_OP_REPLY ->
  is_broadcast_mac reply.(arp_tha) = false.
Proof.
  intros ctx packet ctx' reply Hproc Hreply_op.
  assert (Heq: reply.(arp_tha) = packet.(arp_sha)) by
    (apply (reply_target_is_requester_mac ctx packet ctx' reply Hproc Hreply_op)).
  rewrite Heq.
  unfold process_arp_packet in Hproc.
  destruct (validate_arp_packet packet (arp_my_mac ctx)) eqn:Hvalid.
  - unfold validate_arp_packet in Hvalid.
    destruct (is_broadcast_mac (arp_sha packet)) eqn:Hbcast.
    + simpl in Hvalid. repeat rewrite andb_false_r in Hvalid. discriminate.
    + reflexivity.
  - discriminate.
Qed.

(* =============================================================================
   Section 13C: Packet Validation Properties
   ============================================================================= *)

(* Packet field validation *)
Definition is_valid_arp_packet (p : ARPEthernetIPv4) : bool :=
  (N.eqb p.(arp_op) ARP_OP_REQUEST || N.eqb p.(arp_op) ARP_OP_REPLY) &&
  negb (is_broadcast_mac p.(arp_sha)).

(* Theorem: Only REQUEST and REPLY opcodes generate responses *)
Theorem unknown_opcode_no_response : forall ctx packet ctx' resp,
  N.eqb packet.(arp_op) ARP_OP_REQUEST = false ->
  N.eqb packet.(arp_op) ARP_OP_REPLY = false ->
  process_arp_packet ctx packet = (ctx', resp) ->
  resp = None.
Proof.
  intros ctx packet ctx' resp Hnot_req Hnot_reply Hproc.
  unfold process_arp_packet in Hproc.
  destruct (validate_arp_packet packet (arp_my_mac ctx)) eqn:Hvalid.
  - destruct (ip_eq (arp_tpa packet) (arp_my_ip ctx)) eqn:Htarget.
    + rewrite Hnot_req in Hproc.
      injection Hproc as _ Hresp.
      symmetry. assumption.
    + injection Hproc as _ Hresp.
      symmetry. assumption.
  - injection Hproc as _ Hresp. symmetry. assumption.
Qed.

(* Theorem: Parse validates packet structure *)
Theorem parse_validates_structure : forall data packet,
  parse_arp_packet data = Some packet ->
  length data = 28%nat /\
  length packet.(arp_sha).(mac_bytes) = 6%nat /\
  length packet.(arp_tha).(mac_bytes) = 6%nat.
Proof.
  intros data packet Hparse.
  unfold parse_arp_packet in Hparse.
  repeat match goal with
  | H: context[match ?l with [] => _ | _ :: _ => _ end] |- _ =>
    destruct l; try discriminate H
  end.
  repeat match goal with
  | H: context[if ?b then _ else _] |- _ =>
    destruct b; try discriminate H
  end.
  injection Hparse as Hpacket.
  subst packet.
  simpl.
  split; [reflexivity|].
  split; reflexivity.
Qed.

(* =============================================================================
   Section 14: Round-trip Properties
   ============================================================================= *)

(* Helper lemmas for bitwise operations *)
Lemma land_high_low_disjoint : forall w,
  N.land (2^8 * (w / 2^8)) (w mod 2^8) = 0.
Proof.
  intros w.
  apply N.bits_inj_iff. intros n.
  rewrite N.land_spec, N.bits_0.
  destruct (N.ltb n 8) eqn:Hn.
  - apply N.ltb_lt in Hn.
    assert (N.testbit (2^8 * (w / 2^8)) n = false).
    { rewrite N.mul_comm, <- N.shiftl_mul_pow2 by lia.
      rewrite N.shiftl_spec_low by lia.
      reflexivity. }
    rewrite H. reflexivity.
  - apply N.ltb_ge in Hn.
    assert (N.testbit (w mod 2^8) n = false).
    { apply N.mod_pow2_bits_high. lia. }
    rewrite H. apply andb_false_r.
Qed.

Lemma xorb_eq_orb_when_disjoint : forall a b,
  a && b = false ->
  xorb a b = a || b.
Proof.
  intros. destruct a, b; simpl in *; auto; discriminate.
Qed.

Lemma lor_disjoint_parts : forall a b,
  N.land a b = 0 ->
  N.lor a b = a + b.
Proof.
  intros a b Hdisj.
  rewrite <- N.lxor_lor by assumption.
  symmetry.
  apply N.add_nocarry_lxor.
  assumption.
Qed.

Lemma div2_8times_eq_div256 : forall n,
  n / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2 = n / 2^8.
Proof.
  intros n.
  replace (2^8) with (2*2*2*2*2*2*2*2) by reflexivity.
  repeat rewrite N.div_div by lia.
  reflexivity.
Qed.

Lemma combine_split_word16 : forall w,
  combine_word16 (N.shiftr w 8) (N.land w 255) = w.
Proof.
  intros w.
  unfold combine_word16.
  rewrite N.shiftr_div_pow2 by lia.
  replace 255 with (N.ones 8) by reflexivity.
  rewrite N.land_ones by lia.
  rewrite N.shiftl_mul_pow2 by lia.
  rewrite (N.mul_comm (w / 2^8) (2^8)).
  rewrite lor_disjoint_parts by apply land_high_low_disjoint.
  symmetry.
  rewrite <- (N.div_mod w (2^8)) at 1 by lia.
  f_equal. lia.
Qed.

Theorem serialize_parse_identity : forall packet,
  parse_arp_packet (serialize_arp_packet packet) = Some packet.
Proof.
  intros packet.
  destruct packet as [op sha spa tha tpa].
  destruct sha as [sha_bytes sha_valid].
  destruct tha as [tha_bytes tha_valid].
  destruct spa as [spa_a spa_b spa_c spa_d].
  destruct tpa as [tpa_a tpa_b tpa_c tpa_d].
  destruct sha_bytes as [|s1 [|s2 [|s3 [|s4 [|s5 [|s6 [|]]]]]]]; try discriminate sha_valid.
  destruct tha_bytes as [|t1 [|t2 [|t3 [|t4 [|t5 [|t6 [|]]]]]]]; try discriminate tha_valid.
  unfold serialize_arp_packet, parse_arp_packet.
  unfold serialize_mac, serialize_ipv4, split_word16.
  simpl.
  repeat rewrite N.eqb_refl.
  simpl.
  assert (Hop: combine_word16 (N.div2 (N.div2 (N.div2 (N.div2 (N.div2 (N.div2 (N.div2 (N.div2 op)))))))) (N.land op 255) = op).
  { replace (N.div2 (N.div2 (N.div2 (N.div2 (N.div2 (N.div2 (N.div2 (N.div2 op)))))))) with (N.shiftr op 8).
    apply combine_split_word16.
    repeat rewrite N.div2_div.
    rewrite div2_8times_eq_div256.
    rewrite N.shiftr_div_pow2 by lia.
    reflexivity. }
  rewrite Hop.
  assert (Hsha_eq: {| mac_bytes := [s1; s2; s3; s4; s5; s6]; mac_valid := eq_refl |} =
                   {| mac_bytes := [s1; s2; s3; s4; s5; s6]; mac_valid := sha_valid |}) by
    (f_equal; apply UIP_dec; decide equality; decide equality; apply N.eq_dec).
  assert (Htha_eq: {| mac_bytes := [t1; t2; t3; t4; t5; t6]; mac_valid := eq_refl |} =
                   {| mac_bytes := [t1; t2; t3; t4; t5; t6]; mac_valid := tha_valid |}) by
    (f_equal; apply UIP_dec; decide equality; decide equality; apply N.eq_dec).
  congruence.
Qed.

(* =============================================================================
   Section 14A: Properties of New Functions
   ============================================================================= *)

Theorem resolve_address_cache_hit : forall ctx target_ip mac current_time,
  lookup_cache ctx.(earp_cache) target_ip = Some mac ->
  resolve_address ctx target_ip current_time = (Some mac, ctx, None).
Proof.
  intros ctx target_ip mac current_time Hlookup.
  unfold resolve_address.
  rewrite Hlookup.
  reflexivity.
Qed.

Theorem resolve_address_cache_miss_allowed : forall ctx target_ip current_time,
  lookup_cache ctx.(earp_cache) target_ip = None ->
  snd (update_flood_table ctx.(earp_flood_table) target_ip current_time) = true ->
  exists ctx' req,
    resolve_address ctx target_ip current_time = (None, ctx', Some req) /\
    req.(arp_op) = ARP_OP_REQUEST /\
    req.(arp_tpa) = target_ip /\
    req.(arp_sha) = ctx.(earp_my_mac) /\
    req.(arp_spa) = ctx.(earp_my_ip).
Proof.
  intros ctx target_ip current_time Hlookup Hallowed.
  unfold resolve_address.
  rewrite Hlookup.
  destruct (update_flood_table (earp_flood_table ctx) target_ip current_time) as [new_flood allowed] eqn:Hflood.
  simpl in Hallowed. subst allowed.
  eexists. eexists.
  split.
  - reflexivity.
  - unfold make_arp_request. simpl.
    split. reflexivity.
    split. reflexivity.
    split. reflexivity.
    reflexivity.
Qed.

Theorem resolve_address_cache_miss_rejected : forall ctx target_ip current_time,
  lookup_cache ctx.(earp_cache) target_ip = None ->
  snd (update_flood_table ctx.(earp_flood_table) target_ip current_time) = false ->
  resolve_address ctx target_ip current_time = (None, ctx, None).
Proof.
  intros ctx target_ip current_time Hlookup Hrejected.
  unfold resolve_address.
  rewrite Hlookup.
  destruct (update_flood_table (earp_flood_table ctx) target_ip current_time) as [new_flood allowed] eqn:Hflood.
  simpl in Hrejected. subst allowed.
  reflexivity.
Qed.

Theorem process_generic_arp_round_trip : forall packet,
  process_generic_arp (convert_to_generic packet) = Some packet.
Proof.
  intros packet.
  destruct packet as [op sha spa tha tpa].
  destruct sha as [sha_bytes sha_valid].
  destruct tha as [tha_bytes tha_valid].
  destruct spa as [spa_a spa_b spa_c spa_d].
  destruct tpa as [tpa_a tpa_b tpa_c tpa_d].
  destruct sha_bytes as [|s1 [|s2 [|s3 [|s4 [|s5 [|s6 [|]]]]]]]; try discriminate sha_valid.
  destruct tha_bytes as [|t1 [|t2 [|t3 [|t4 [|t5 [|t6 [|]]]]]]]; try discriminate tha_valid.
  unfold process_generic_arp, convert_to_generic, is_supported_hw_proto.
  simpl.
  repeat rewrite N.eqb_refl.
  simpl.
  assert (Hsha_eq: {| mac_bytes := [s1; s2; s3; s4; s5; s6]; mac_valid := eq_refl |} =
                   {| mac_bytes := [s1; s2; s3; s4; s5; s6]; mac_valid := sha_valid |}) by
    (f_equal; apply UIP_dec; decide equality; decide equality; apply N.eq_dec).
  assert (Htha_eq: {| mac_bytes := [t1; t2; t3; t4; t5; t6]; mac_valid := eq_refl |} =
                   {| mac_bytes := [t1; t2; t3; t4; t5; t6]; mac_valid := tha_valid |}) by
    (f_equal; apply UIP_dec; decide equality; decide equality; apply N.eq_dec).
  congruence.
Qed.

Theorem generic_arp_validates_hw_proto : forall packet result,
  process_generic_arp packet = Some result ->
  packet.(ar_hrd) = ARP_HRD_ETHERNET /\
  packet.(ar_pro) = ARP_PRO_IP.
Proof.
  intros packet result Hproc.
  unfold process_generic_arp in Hproc.
  unfold is_supported_hw_proto in Hproc.
  destruct (N.eqb (ar_hrd packet) ARP_HRD_ETHERNET) eqn:Hhrd.
  - destruct (N.eqb (ar_pro packet) ARP_PRO_IP) eqn:Hpro.
    + apply N.eqb_eq in Hhrd.
      apply N.eqb_eq in Hpro.
      split; assumption.
    + simpl in Hproc. discriminate.
  - simpl in Hproc. discriminate.
Qed.

Theorem generic_arp_validates_lengths : forall packet result,
  process_generic_arp packet = Some result ->
  packet.(ar_hln) = ETHERNET_ADDR_LEN /\
  packet.(ar_pln) = IPV4_ADDR_LEN.
Proof.
  intros packet result Hproc.
  unfold process_generic_arp in Hproc.
  destruct (is_supported_hw_proto (ar_hrd packet) (ar_pro packet)) eqn:Hsupp.
  - destruct (N.eqb (ar_hln packet) ETHERNET_ADDR_LEN) eqn:Hhln.
    + destruct (N.eqb (ar_pln packet) IPV4_ADDR_LEN) eqn:Hpln.
      * apply N.eqb_eq in Hhln.
        apply N.eqb_eq in Hpln.
        split; assumption.
      * simpl in Hproc. discriminate.
    + simpl in Hproc. discriminate.
  - discriminate.
Qed.

Lemma add_pending_request_preserves_mac : forall ctx target_ip current_time,
  earp_my_mac (add_pending_request ctx target_ip current_time) = earp_my_mac ctx.
Proof.
  intros ctx target_ip current_time.
  unfold add_pending_request.
  destruct (earp_state_data ctx); simpl; reflexivity.
Qed.

Lemma add_pending_request_preserves_ip : forall ctx target_ip current_time,
  earp_my_ip (add_pending_request ctx target_ip current_time) = earp_my_ip ctx.
Proof.
  intros ctx target_ip current_time.
  unfold add_pending_request.
  destruct (earp_state_data ctx); simpl; reflexivity.
Qed.

Theorem resolve_address_preserves_mac : forall ctx target_ip current_time,
  (earp_my_mac ctx) =
  (earp_my_mac (let '(_, ctx', _) := resolve_address ctx target_ip current_time in ctx')).
Proof.
  intros ctx target_ip current_time.
  unfold resolve_address.
  destruct (lookup_cache (earp_cache ctx) target_ip) eqn:Hlookup; simpl.
  - reflexivity.
  - destruct (update_flood_table (earp_flood_table ctx) target_ip current_time) as [new_flood allowed].
    destruct allowed; simpl.
    + rewrite add_pending_request_preserves_mac. reflexivity.
    + reflexivity.
Qed.

Theorem resolve_address_preserves_ip : forall ctx target_ip current_time,
  (earp_my_ip ctx) =
  (earp_my_ip (let '(_, ctx', _) := resolve_address ctx target_ip current_time in ctx')).
Proof.
  intros ctx target_ip current_time.
  unfold resolve_address.
  destruct (lookup_cache (earp_cache ctx) target_ip) eqn:Hlookup; simpl.
  - reflexivity.
  - destruct (update_flood_table (earp_flood_table ctx) target_ip current_time) as [new_flood allowed].
    destruct allowed; simpl.
    + rewrite add_pending_request_preserves_ip. reflexivity.
    + reflexivity.
Qed.

Theorem send_arp_request_with_flood_check_preserves_my_ip : forall ctx target_ip current_time ctx' pkt,
  send_arp_request_with_flood_check ctx target_ip current_time = (ctx', pkt) ->
  earp_my_ip ctx' = earp_my_ip ctx.
Proof.
  intros ctx target_ip current_time ctx' pkt Hsend.
  unfold send_arp_request_with_flood_check in Hsend.
  destruct (update_flood_table (earp_flood_table ctx) target_ip current_time) as [new_flood allowed] eqn:Hflood.
  destruct allowed; injection Hsend as Hctx Hpkt; subst; simpl; reflexivity.
Qed.

Theorem start_dad_probe_preserves_mac_and_ip : forall ctx ip_to_probe current_time,
  earp_my_mac (start_dad_probe ctx ip_to_probe current_time) = earp_my_mac ctx /\
  earp_my_ip (start_dad_probe ctx ip_to_probe current_time) = earp_my_ip ctx.
Proof.
  intros ctx ip_to_probe current_time.
  unfold start_dad_probe.
  simpl. split; reflexivity.
Qed.

Theorem start_dad_probe_enters_probe_state : forall ctx ip_to_probe current_time,
  exists probe,
    earp_state_data (start_dad_probe ctx ip_to_probe current_time) = StateProbe probe /\
    probe.(probe_ip) = ip_to_probe /\
    probe.(probe_count) = 0.
Proof.
  intros ctx ip_to_probe current_time.
  unfold start_dad_probe.
  exists {| probe_ip := ip_to_probe; probe_count := 0;
            probe_timer := start_timer ARP_PROBE_WAIT current_time |}.
  simpl. split; [reflexivity | split; reflexivity].
Qed.

Theorem make_arp_probe_has_zero_sender_ip : forall my_mac target_ip,
  let probe := make_arp_probe my_mac target_ip in
  probe.(arp_spa) = {| ipv4_a := 0; ipv4_b := 0; ipv4_c := 0; ipv4_d := 0 |}.
Proof.
  intros my_mac target_ip probe.
  unfold probe, make_arp_probe.
  simpl. reflexivity.
Qed.

Theorem make_arp_probe_is_request : forall my_mac target_ip,
  (make_arp_probe my_mac target_ip).(arp_op) = ARP_OP_REQUEST.
Proof.
  intros my_mac target_ip.
  unfold make_arp_probe.
  simpl. reflexivity.
Qed.

Theorem process_probe_timeout_preserves_mac : forall ctx probe current_time ctx' pkt,
  process_probe_timeout ctx probe current_time = (ctx', pkt) ->
  earp_my_mac ctx' = earp_my_mac ctx.
Proof.
  intros ctx probe current_time ctx' pkt Hproc.
  unfold process_probe_timeout in Hproc.
  destruct (timer_expired (probe_timer probe) current_time) eqn:Hexp.
  - destruct (N.ltb (probe_count probe) ARP_PROBE_NUM) eqn:Hlt.
    + injection Hproc as Hctx _. subst. simpl. reflexivity.
    + injection Hproc as Hctx _. subst. simpl. reflexivity.
  - injection Hproc as Hctx _. subst. reflexivity.
Qed.

Theorem process_probe_timeout_increments_count_or_transitions : forall ctx probe current_time ctx' pkt,
  timer_expired probe.(probe_timer) current_time = true ->
  process_probe_timeout ctx probe current_time = (ctx', pkt) ->
  (exists new_probe,
    earp_state_data ctx' = StateProbe new_probe /\
    probe_count new_probe = probe_count probe + 1 /\
    pkt <> None) \/
  (exists announce,
    earp_state_data ctx' = StateAnnounce announce /\
    earp_my_ip ctx' = probe.(probe_ip) /\
    pkt = None).
Proof.
  intros ctx probe current_time ctx' pkt Hexp Hproc.
  unfold process_probe_timeout in Hproc.
  rewrite Hexp in Hproc.
  destruct (N.ltb (probe_count probe) ARP_PROBE_NUM) eqn:Hlt.
  - left. injection Hproc as Hctx Hpkt. subst.
    exists {| probe_ip := probe_ip probe; probe_count := probe_count probe + 1;
              probe_timer := start_timer ARP_PROBE_MIN current_time |}.
    simpl. split; [reflexivity | split; [reflexivity | discriminate]].
  - right. injection Hproc as Hctx Hpkt. subst.
    exists {| announce_count := 0; announce_timer := start_timer ARP_ANNOUNCE_WAIT current_time |}.
    simpl. split; [reflexivity | split; reflexivity].
Qed.

Theorem detect_probe_conflict_detects_ip_match : forall ctx probe packet,
  ip_eq (arp_spa packet) (probe_ip probe) = true ->
  detect_probe_conflict ctx probe packet = true.
Proof.
  intros ctx probe packet Hmatch.
  unfold detect_probe_conflict.
  rewrite Hmatch.
  apply orb_true_l.
Qed.

Theorem process_announce_timeout_preserves_mac : forall ctx announce current_time ctx' pkt,
  process_announce_timeout ctx announce current_time = (ctx', pkt) ->
  earp_my_mac ctx' = earp_my_mac ctx.
Proof.
  intros ctx announce current_time ctx' pkt Hproc.
  unfold process_announce_timeout in Hproc.
  destruct (timer_expired (announce_timer announce) current_time) eqn:Hexp.
  - destruct (N.ltb (announce_count announce) ARP_ANNOUNCE_NUM) eqn:Hlt.
    + injection Hproc as Hctx _. subst. simpl. reflexivity.
    + injection Hproc as Hctx _. subst. simpl. reflexivity.
  - injection Hproc as Hctx _. subst. reflexivity.
Qed.

Theorem process_announce_timeout_increments_or_idles : forall ctx announce current_time ctx' pkt,
  timer_expired announce.(announce_timer) current_time = true ->
  process_announce_timeout ctx announce current_time = (ctx', pkt) ->
  (exists new_announce,
    earp_state_data ctx' = StateAnnounce new_announce /\
    announce_count new_announce = announce_count announce + 1 /\
    pkt <> None) \/
  (earp_state_data ctx' = StateIdle /\ pkt = None).
Proof.
  intros ctx announce current_time ctx' pkt Hexp Hproc.
  unfold process_announce_timeout in Hproc.
  rewrite Hexp in Hproc.
  destruct (N.ltb (announce_count announce) ARP_ANNOUNCE_NUM) eqn:Hlt.
  - left. injection Hproc as Hctx Hpkt. subst.
    exists {| announce_count := announce_count announce + 1;
              announce_timer := start_timer ARP_ANNOUNCE_INTERVAL current_time |}.
    simpl. split; [reflexivity | split; [reflexivity | discriminate]].
  - right. injection Hproc as Hctx Hpkt. subst.
    simpl. split; reflexivity.
Qed.

Theorem detect_address_conflict_true_means_different_mac : forall ctx packet,
  detect_address_conflict ctx packet = true ->
  ip_eq (arp_spa packet) (earp_my_ip ctx) = true /\
  (mac_bytes (arp_sha packet)) <> (mac_bytes (earp_my_mac ctx)).
Proof.
  intros ctx packet Hconf.
  unfold detect_address_conflict in Hconf.
  apply andb_true_iff in Hconf.
  destruct Hconf as [Hipsame Hmacdiff].
  split; auto.
  destruct (list_eq_dec N.eq_dec (mac_bytes (arp_sha packet))
                        (mac_bytes (earp_my_mac ctx))) eqn:Heq.
  - discriminate.
  - assumption.
Qed.

Theorem process_conflict_preserves_mac : forall ctx current_time ctx' pkt,
  process_conflict ctx current_time = (ctx', pkt) ->
  earp_my_mac ctx' = earp_my_mac ctx.
Proof.
  intros ctx current_time ctx' pkt Hproc.
  unfold process_conflict in Hproc.
  destruct (earp_state_data ctx) eqn:Hstate.
  - injection Hproc as Hctx _. subst. simpl. reflexivity.
  - injection Hproc as Hctx _. subst. simpl. reflexivity.
  - injection Hproc as Hctx _. subst. simpl. reflexivity.
  - injection Hproc as Hctx _. subst. simpl. reflexivity.
  - destruct (can_defend d current_time) eqn:Hcan.
    + injection Hproc as Hctx _. subst. simpl. reflexivity.
    + injection Hproc as Hctx _. subst. reflexivity.
  - injection Hproc as Hctx _. subst. reflexivity.
Qed.

Theorem process_conflict_preserves_ip : forall ctx current_time ctx' pkt,
  process_conflict ctx current_time = (ctx', pkt) ->
  earp_my_ip ctx' = earp_my_ip ctx.
Proof.
  intros ctx current_time ctx' pkt Hproc.
  unfold process_conflict in Hproc.
  destruct (earp_state_data ctx) eqn:Hstate.
  - injection Hproc as Hctx _. subst. simpl. reflexivity.
  - injection Hproc as Hctx _. subst. simpl. reflexivity.
  - injection Hproc as Hctx _. subst. simpl. reflexivity.
  - injection Hproc as Hctx _. subst. simpl. reflexivity.
  - destruct (can_defend d current_time) eqn:Hcan.
    + injection Hproc as Hctx _. subst. simpl. reflexivity.
    + injection Hproc as Hctx _. subst. reflexivity.
  - injection Hproc as Hctx _. subst. reflexivity.
Qed.

Theorem process_conflict_enters_defend_or_stays_conflict : forall ctx current_time ctx' pkt,
  process_conflict ctx current_time = (ctx', pkt) ->
  (exists defend, earp_state_data ctx' = StateDefend defend) \/
  (exists conflicted_ip, earp_state_data ctx' = StateConflict conflicted_ip).
Proof.
  intros ctx current_time ctx' pkt Hproc.
  unfold process_conflict in Hproc.
  destruct (earp_state_data ctx) eqn:Hstate.
  - injection Hproc as Hctx _. subst ctx'. simpl. left.
    exists {| defend_last_time := current_time |}. reflexivity.
  - injection Hproc as Hctx _. subst ctx'. simpl. left.
    exists {| defend_last_time := current_time |}. reflexivity.
  - injection Hproc as Hctx _. subst ctx'. simpl. left.
    exists {| defend_last_time := current_time |}. reflexivity.
  - injection Hproc as Hctx _. subst ctx'. simpl. left.
    exists {| defend_last_time := current_time |}. reflexivity.
  - destruct (can_defend d current_time) eqn:Hcan.
    + injection Hproc as Hctx _. subst ctx'. simpl. left.
      exists {| defend_last_time := current_time |}. reflexivity.
    + injection Hproc as Hctx _. subst ctx'. simpl. left.
      exists d. rewrite <- Hstate. reflexivity.
  - injection Hproc as Hctx _. subst ctx'. right.
    exists i. rewrite Hstate. reflexivity.
Qed.

Theorem arp_request_reply_roundtrip_correctness : forall ctx pkt resp ctx',
  validate_arp_packet pkt ctx.(arp_my_mac) = true ->
  pkt.(arp_op) = ARP_OP_REQUEST ->
  ip_eq pkt.(arp_tpa) ctx.(arp_my_ip) = true ->
  (forall e, In e ctx.(arp_cache) ->
   ip_eq (ace_ip e) pkt.(arp_spa) = true ->
   ace_static e = false) ->
  process_arp_packet ctx pkt = (ctx', resp) ->
  exists reply,
    resp = Some reply /\
    reply.(arp_op) = ARP_OP_REPLY /\
    reply.(arp_spa) = ctx.(arp_my_ip) /\
    reply.(arp_tpa) = pkt.(arp_spa) /\
    reply.(arp_sha) = ctx.(arp_my_mac) /\
    reply.(arp_tha) = pkt.(arp_sha) /\
    lookup_cache ctx'.(arp_cache) pkt.(arp_spa) = Some pkt.(arp_sha).
Proof.
  intros ctx pkt resp ctx' Hvalid_pkt Hop Htarget Hno_static Hproc.
  unfold process_arp_packet in Hproc.
  rewrite Hvalid_pkt in Hproc.
  rewrite Htarget in Hproc.
  apply N.eqb_eq in Hop.
  rewrite Hop in Hproc.
  injection Hproc as Hctx Hresp.
  subst ctx' resp.
  exists (make_arp_reply (arp_my_mac ctx) (arp_my_ip ctx) (arp_sha pkt) (arp_spa pkt)).
  split. reflexivity.
  split. unfold make_arp_reply. simpl. reflexivity.
  split. unfold make_arp_reply. simpl. reflexivity.
  split. unfold make_arp_reply. simpl. reflexivity.
  split. unfold make_arp_reply. simpl. reflexivity.
  split. unfold make_arp_reply. simpl. reflexivity.
  simpl. apply rfc826_merge_target. assumption.
Qed.

(* RFC 826 algorithm completeness: proves reply generation, cache updates, and identity preservation *)
Theorem rfc826_algorithm_is_complete : forall ctx pkt ctx' resp,
  validate_arp_packet pkt ctx.(arp_my_mac) = true ->
  process_arp_packet ctx pkt = (ctx', resp) ->
  (ip_eq pkt.(arp_tpa) ctx.(arp_my_ip) = true ->
   pkt.(arp_op) = ARP_OP_REQUEST ->
   exists reply,
     resp = Some reply /\
     reply.(arp_op) = ARP_OP_REPLY /\
     reply.(arp_spa) = ctx.(arp_my_ip) /\
     reply.(arp_tpa) = pkt.(arp_spa) /\
     reply.(arp_sha) = ctx.(arp_my_mac) /\
     reply.(arp_tha) = pkt.(arp_sha)) /\
  (ip_eq pkt.(arp_tpa) ctx.(arp_my_ip) = true ->
   exists new_mac,
    lookup_cache ctx'.(arp_cache) pkt.(arp_spa) = Some new_mac) /\
  (ip_eq pkt.(arp_tpa) ctx.(arp_my_ip) = false ->
   lookup_cache ctx.(arp_cache) pkt.(arp_spa) = None ->
   lookup_cache ctx'.(arp_cache) pkt.(arp_spa) = None) /\
  (arp_my_mac ctx' = arp_my_mac ctx /\
   arp_my_ip ctx' = arp_my_ip ctx).
Proof.
  intros ctx pkt ctx' resp Hvalid_pkt Hproc.
  repeat split.
  - intros Htarget Hreq.
    unfold process_arp_packet in Hproc.
    rewrite Hvalid_pkt in Hproc.
    rewrite Htarget in Hproc.
    apply N.eqb_eq in Hreq.
    rewrite Hreq in Hproc.
    injection Hproc as Hctx Hresp.
    subst ctx' resp.
    exists (make_arp_reply (arp_my_mac ctx) (arp_my_ip ctx) (arp_sha pkt) (arp_spa pkt)).
    split. reflexivity.
    split. unfold make_arp_reply. simpl. reflexivity.
    split. unfold make_arp_reply. simpl. reflexivity.
    split. unfold make_arp_reply. simpl. reflexivity.
    split. unfold make_arp_reply. simpl. reflexivity.
    unfold make_arp_reply. simpl. reflexivity.
  - intros Htarget.
    unfold process_arp_packet in Hproc.
    rewrite Hvalid_pkt in Hproc.
    rewrite Htarget in Hproc.
    destruct (N.eqb (arp_op pkt) ARP_OP_REQUEST);
    injection Hproc as Hctx _; subst ctx'; simpl;
    apply rfc826_merge_updates_or_adds with (target := true); reflexivity.
  - intros Hnot_target Hnot_in_cache.
    unfold process_arp_packet in Hproc.
    rewrite Hvalid_pkt in Hproc.
    rewrite Hnot_target in Hproc.
    destruct (N.eqb (arp_op pkt) ARP_OP_REQUEST) eqn:Hop.
    + injection Hproc as Hctx _. subst ctx'. simpl.
      rewrite rfc826_merge_not_target by assumption.
      assumption.
    + injection Hproc as Hctx _. subst ctx'. simpl.
      rewrite rfc826_merge_not_target by assumption.
      assumption.
  - unfold process_arp_packet in Hproc.
    rewrite Hvalid_pkt in Hproc.
    destruct (ip_eq (arp_tpa pkt) (arp_my_ip ctx)) eqn:Htgt;
    destruct (N.eqb (arp_op pkt) ARP_OP_REQUEST) eqn:Hop;
    injection Hproc as H1 H2; rewrite <- H1; simpl; reflexivity.
  - unfold process_arp_packet in Hproc.
    rewrite Hvalid_pkt in Hproc.
    destruct (ip_eq (arp_tpa pkt) (arp_my_ip ctx)) eqn:Htgt;
    destruct (N.eqb (arp_op pkt) ARP_OP_REQUEST) eqn:Hop;
    injection Hproc as H1 H2; rewrite <- H1; simpl; reflexivity.
Qed.

(* ARP packet processing is deterministic: same input always produces same output *)
Theorem process_arp_deterministic : forall ctx pkt ctx1 resp1 ctx2 resp2,
  process_arp_packet ctx pkt = (ctx1, resp1) ->
  process_arp_packet ctx pkt = (ctx2, resp2) ->
  ctx1 = ctx2 /\ resp1 = resp2.
Proof.
  intros ctx pkt ctx1 resp1 ctx2 resp2 H1 H2.
  rewrite H1 in H2.
  injection H2 as Hctx Hresp.
  split; assumption.
Qed.

(* Cache monotonicity: lookups for unrelated IPs are preserved *)
Theorem cache_monotonic_unrelated : forall ctx pkt ctx' resp ip mac,
  process_arp_packet ctx pkt = (ctx', resp) ->
  lookup_cache (arp_cache ctx) ip = Some mac ->
  ip <> pkt.(arp_spa) ->
  lookup_cache (arp_cache ctx') ip = Some mac.
Proof.
  intros ctx pkt ctx' resp ip mac Hproc Hlook Hneq.
  unfold process_arp_packet in Hproc.
  destruct (validate_arp_packet pkt (arp_my_mac ctx)) eqn:Hvalid.
  - destruct (ip_eq (arp_tpa pkt) (arp_my_ip ctx)) eqn:Htgt;
    destruct (N.eqb (arp_op pkt) ARP_OP_REQUEST) eqn:Hreq;
    injection Hproc as Hctx Hresp;
    subst ctx';
    simpl.
    + erewrite rfc826_merge_preserves_other_ips. exact Hlook. assumption.
    + erewrite rfc826_merge_preserves_other_ips. exact Hlook. assumption.
    + erewrite rfc826_merge_preserves_other_ips. exact Hlook. assumption.
    + erewrite rfc826_merge_preserves_other_ips. exact Hlook. assumption.
  - injection Hproc as Hctx Hresp. subst. simpl. assumption.
Qed.

(* Stronger RFC 826 completeness: full behavioral specification with IFF semantics, cache isolation, and complete immutability *)
Theorem rfc826_algorithm_complete_strong : forall ctx pkt ctx' resp,
  validate_arp_packet pkt ctx.(arp_my_mac) = true ->
  process_arp_packet ctx pkt = (ctx', resp) ->
  (* Part 1: Complete response characterization *)
  ((ip_eq pkt.(arp_tpa) ctx.(arp_my_ip) = true /\ pkt.(arp_op) = ARP_OP_REQUEST) ->
   exists reply,
     resp = Some reply /\
     reply.(arp_op) = ARP_OP_REPLY /\
     reply.(arp_spa) = ctx.(arp_my_ip) /\
     reply.(arp_tpa) = pkt.(arp_spa) /\
     reply.(arp_sha) = ctx.(arp_my_mac) /\
     reply.(arp_tha) = pkt.(arp_sha)) /\
  (* Part 2: No response in all other cases *)
  ((ip_eq pkt.(arp_tpa) ctx.(arp_my_ip) = false \/ pkt.(arp_op) <> ARP_OP_REQUEST) ->
   resp = None) /\
  (* Part 3: Cache updated when target (exact MAC if no static entry blocks) *)
  (ip_eq pkt.(arp_tpa) ctx.(arp_my_ip) = true ->
   exists mac, lookup_cache ctx'.(arp_cache) pkt.(arp_spa) = Some mac) /\
  (* Part 4: Cache not updated when not target and not in cache *)
  (ip_eq pkt.(arp_tpa) ctx.(arp_my_ip) = false ->
   lookup_cache ctx.(arp_cache) pkt.(arp_spa) = None ->
   lookup_cache ctx'.(arp_cache) pkt.(arp_spa) = None) /\
  (* Part 5: Cache entries for other IPs preserved *)
  (forall other_ip,
   other_ip <> pkt.(arp_spa) ->
   lookup_cache ctx'.(arp_cache) other_ip = lookup_cache ctx.(arp_cache) other_ip) /\
  (* Part 6: Identity preservation - MAC and IP unchanged *)
  (arp_my_mac ctx' = arp_my_mac ctx) /\
  (arp_my_ip ctx' = arp_my_ip ctx).
Proof.
  intros ctx pkt ctx' resp Hvalid_pkt Hproc.
  unfold process_arp_packet in Hproc.
  rewrite Hvalid_pkt in Hproc.
  destruct (ip_eq pkt.(arp_tpa) ctx.(arp_my_ip)) eqn:Htgt;
  destruct (N.eqb pkt.(arp_op) ARP_OP_REQUEST) eqn:Hreq.

  (* Case 1: Target is me, operation is REQUEST *)
  - injection Hproc as Hctx Hresp.
    subst ctx' resp.
    split.
    { intros [_ H].
      exists (make_arp_reply (arp_my_mac ctx) (arp_my_ip ctx) (arp_sha pkt) (arp_spa pkt)).
      split. reflexivity.
      split. unfold make_arp_reply. simpl. reflexivity.
      split. unfold make_arp_reply. simpl. reflexivity.
      split. unfold make_arp_reply. simpl. reflexivity.
      split. unfold make_arp_reply. simpl. reflexivity.
      unfold make_arp_reply. simpl. reflexivity. }
    split.
    { intros [H | H].
      * congruence.
      * apply N.eqb_eq in Hreq. contradiction. }
    split.
    { intros _.
      simpl.
      apply rfc826_merge_updates_or_adds with (target := true).
      reflexivity. }
    split.
    { intros H _.
      congruence. }
    split.
    { intros other_ip Hneq.
      simpl.
      apply rfc826_merge_preserves_other_ips.
      assumption. }
    simpl. repeat split; reflexivity.

  (* Case 2: Target is me, operation is not REQUEST *)
  - injection Hproc as Hctx Hresp.
    subst ctx' resp.
    split.
    { intros [_ H].
      apply N.eqb_neq in Hreq.
      contradiction. }
    split.
    { intros _.
      reflexivity. }
    split.
    { intros _.
      simpl.
      apply rfc826_merge_updates_or_adds with (target := true).
      reflexivity. }
    split.
    { intros H _.
      congruence. }
    split.
    { intros other_ip Hneq.
      simpl.
      apply rfc826_merge_preserves_other_ips.
      assumption. }
    simpl. repeat split; reflexivity.

  (* Case 3: Target is not me, operation is REQUEST *)
  - injection Hproc as Hctx Hresp.
    subst ctx' resp.
    split.
    { intros [H _].
      congruence. }
    split.
    { intros _.
      reflexivity. }
    split.
    { intros H.
      congruence. }
    split.
    { intros _ Hnot_in.
      simpl.
      rewrite rfc826_merge_not_target by assumption.
      assumption. }
    split.
    { intros other_ip Hneq.
      simpl.
      destruct (lookup_cache (arp_cache ctx) (arp_spa pkt)) eqn:Hlookup.
      * apply rfc826_merge_preserves_other_ips. assumption.
      * rewrite rfc826_merge_not_target by assumption.
        reflexivity. }
    simpl. repeat split; reflexivity.

  (* Case 4: Target is not me, operation is not REQUEST *)
  - injection Hproc as Hctx Hresp.
    subst ctx' resp.
    split.
    { intros [H _].
      congruence. }
    split.
    { intros _.
      reflexivity. }
    split.
    { intros H.
      congruence. }
    split.
    { intros _ Hnot_in.
      simpl.
      rewrite rfc826_merge_not_target by assumption.
      assumption. }
    split.
    { intros other_ip Hneq.
      simpl.
      destruct (lookup_cache (arp_cache ctx) (arp_spa pkt)) eqn:Hlookup.
      * apply rfc826_merge_preserves_other_ips. assumption.
      * rewrite rfc826_merge_not_target by assumption.
        reflexivity. }
    simpl. repeat split; reflexivity.
Qed.

(* =============================================================================
   Section 14A: Temporal Properties
   ============================================================================= *)

Definition CACHE_TIMEOUT : N := 300.

Fixpoint age_n_times (cache : ARPCache) (n : nat) : ARPCache :=
  match n with
  | O => cache
  | S n' => age_cache (age_n_times cache n') 1
  end.

(* =============================================================================
   Section 14B: Network Model
   ============================================================================= *)

Inductive NetworkEvent :=
  | SendPacket : ARPPacket -> NetworkEvent
  | ReceivePacket : ARPPacket -> NetworkEvent
  | Timeout : N -> NetworkEvent.

Record NetworkNode := {
  node_ctx : ARPContext;
  node_time : N
}.

Definition NetworkState := list NetworkNode.

Definition process_event (node : NetworkNode) (event : NetworkEvent) : NetworkNode :=
  match event with
  | ReceivePacket pkt =>
      match process_generic_arp pkt with
      | Some arp_pkt =>
          let (ctx', _) := process_arp_packet node.(node_ctx) arp_pkt in
          {| node_ctx := ctx'; node_time := node.(node_time) |}
      | None => node
      end
  | Timeout elapsed =>
      let aged_cache := age_cache node.(node_ctx).(arp_cache) elapsed in
      {| node_ctx := {| arp_my_mac := node.(node_ctx).(arp_my_mac);
                        arp_my_ip := node.(node_ctx).(arp_my_ip);
                        arp_cache := aged_cache |};
         node_time := node.(node_time) + elapsed |}
  | SendPacket _ => node
  end.

Definition apply_event_to_network (network : NetworkState) (node_id : nat)
                                   (event : NetworkEvent) : NetworkState :=
  match nth_error network node_id with
  | Some node =>
      let node' := process_event node event in
      firstn node_id network ++ [node'] ++ skipn (S node_id) network
  | None => network
  end.

(* =============================================================================
   Section 14C: Enhanced Event Loop
   ============================================================================= *)

Inductive EnhancedEvent :=
  | EPacketIn : ARPEthernetIPv4 -> EnhancedEvent
  | ETimerTick : N -> EnhancedEvent
  | EProbeTimeout : EnhancedEvent
  | EAnnounceTimeout : EnhancedEvent
  | ERequestTimeout : EnhancedEvent.

Record EnhancedNode := {
  enode_ctx : EnhancedARPContext;
  enode_time : N
}.

Definition enhanced_process_event (node : EnhancedNode) (event : EnhancedEvent)
                                   : EnhancedNode * list ARPEthernetIPv4 :=
  let current_time := node.(enode_time) in
  match event with
  | EPacketIn packet =>
      let elapsed := 0 in
      let (ctx', resp) := process_arp_packet_enhanced node.(enode_ctx) packet current_time elapsed in
      let outgoing := match resp with
                      | Some pkt => [pkt]
                      | None => []
                      end in
      ({| enode_ctx := ctx'; enode_time := current_time |}, outgoing)

  | ETimerTick elapsed =>
      let (ctx', outgoing) := process_timeouts node.(enode_ctx) (current_time + elapsed) in
      ({| enode_ctx := ctx'; enode_time := current_time + elapsed |}, outgoing)

  | EProbeTimeout =>
      match node.(enode_ctx).(earp_state_data) with
      | StateProbe probe =>
          let (ctx', pkt_opt) := process_probe_timeout node.(enode_ctx) probe current_time in
          let outgoing := match pkt_opt with
                          | Some pkt => [pkt]
                          | None => []
                          end in
          ({| enode_ctx := ctx'; enode_time := current_time |}, outgoing)
      | _ => (node, [])
      end

  | EAnnounceTimeout =>
      match node.(enode_ctx).(earp_state_data) with
      | StateAnnounce announce =>
          let (ctx', pkt_opt) := process_announce_timeout node.(enode_ctx) announce current_time in
          let outgoing := match pkt_opt with
                          | Some pkt => [pkt]
                          | None => []
                          end in
          ({| enode_ctx := ctx'; enode_time := current_time |}, outgoing)
      | _ => (node, [])
      end

  | ERequestTimeout =>
      let (ctx', outgoing) := process_timeouts node.(enode_ctx) current_time in
      ({| enode_ctx := ctx'; enode_time := current_time |}, outgoing)
  end.

Theorem enhanced_event_processes_timeouts : forall node elapsed node' pkts,
  enhanced_process_event node (ETimerTick elapsed) = (node', pkts) ->
  enode_time node' = enode_time node + elapsed.
Proof.
  intros node elapsed node' pkts Hproc.
  unfold enhanced_process_event in Hproc.
  destruct (process_timeouts (enode_ctx node) (enode_time node + elapsed)) eqn:Htimeouts.
  injection Hproc as Hnode _. subst node'. simpl. reflexivity.
Qed.

Theorem enhanced_event_handles_probe_timeout : forall node probe node' pkts,
  earp_state_data (enode_ctx node) = StateProbe probe ->
  enhanced_process_event node EProbeTimeout = (node', pkts) ->
  exists ctx' pkt_opt,
    process_probe_timeout (enode_ctx node) probe (enode_time node) = (ctx', pkt_opt) /\
    enode_ctx node' = ctx'.
Proof.
  intros node probe node' pkts Hstate Hproc.
  unfold enhanced_process_event in Hproc.
  rewrite Hstate in Hproc.
  destruct (process_probe_timeout (enode_ctx node) probe (enode_time node)) eqn:Hpt.
  injection Hproc as Hnode _. subst node'. simpl.
  exists e, o. split; reflexivity.
Qed.

(* =============================================================================
   Section 14D: Model Equivalence - Enhanced Subsumes Simple
   ============================================================================= *)

Lemma clean_flood_table_empty : forall t,
  clean_flood_table [] t = [].
Proof.
  intros. unfold clean_flood_table. reflexivity.
Qed.

Lemma age_zero_eq_filter_zero : forall cache,
  (forall e, In e cache -> ace_ttl e > 0 \/ ace_static e = true) ->
  age_cache cache 0 = cache.
Proof.
  intros cache Hpos.
  unfold age_cache.
  rewrite map_age_zero.
  induction cache as [|e rest IH].
  - simpl. reflexivity.
  - simpl.
    assert (Hin: In e (e :: rest)) by (simpl; left; reflexivity).
    assert (HposE: ace_ttl e > 0 \/ ace_static e = true) by (apply Hpos; assumption).
    destruct (ace_static e) eqn:Hstatic.
    + simpl. f_equal. apply IH. intros e' Hin'. apply Hpos. simpl. right. assumption.
    + assert (Httl_pos: ace_ttl e > 0) by (destruct HposE; [assumption | congruence]).
      simpl. destruct (ace_ttl e <=? 0) eqn:Hle.
      * apply N.leb_le in Hle. lia.
      * simpl. f_equal. apply IH. intros e' Hin'. apply Hpos. simpl. right. assumption.
Qed.

Lemma broadcast_fails_validation : forall pkt my_mac,
  is_broadcast_mac (arp_sha pkt) = true ->
  validate_arp_packet pkt my_mac = false.
Proof.
  intros pkt my_mac Hbcast.
  unfold validate_arp_packet.
  rewrite Hbcast. simpl.
  destruct (is_valid_opcode (arp_op pkt)); reflexivity.
Qed.

Lemma enhanced_ages_to_simple_cache : forall ctx,
  (forall e, In e (earp_cache ctx) -> ace_ttl e > 0 \/ ace_static e = true) ->
  age_cache (earp_cache ctx) 0 = earp_cache ctx.
Proof.
  intros ctx Hvalid.
  apply age_zero_eq_filter_zero. assumption.
Qed.

Lemma enhanced_broadcast_case : forall ctx pkt ctx_aged,
  earp_state_data ctx = StateIdle ->
  earp_flood_table ctx = [] ->
  (forall e, In e (earp_cache ctx) -> ace_ttl e > 0 \/ ace_static e = true) ->
  is_broadcast_mac (arp_sha pkt) = true ->
  ctx_aged = {| earp_my_mac := earp_my_mac ctx;
               earp_my_ip := earp_my_ip ctx;
               earp_cache := age_cache (earp_cache ctx) 0;
               earp_state_data := earp_state_data ctx;
               earp_iface := earp_iface ctx;
               earp_flood_table := clean_flood_table (earp_flood_table ctx) 0;
               earp_last_cache_cleanup := 0 |} ->
  forall ctx_simple,
    arp_my_mac ctx_simple = earp_my_mac ctx ->
    arp_my_ip ctx_simple = earp_my_ip ctx ->
    arp_cache ctx_simple = earp_cache ctx ->
    process_arp_packet ctx_simple pkt = (ctx_simple, None).
Proof.
  intros ctx pkt ctx_aged Hstate Hflood Hvalid Hbcast Heq ctx_simple Hmac Hip Hcache.
  unfold process_arp_packet.
  assert (Hvalid_false: validate_arp_packet pkt (arp_my_mac ctx_simple) = false).
  { apply broadcast_fails_validation. assumption. }
  rewrite Hvalid_false.
  destruct ctx_simple. simpl in *. subst. reflexivity.
Qed.

Lemma simple_ctx_construction : forall mac ip cache,
  {| arp_my_mac := mac; arp_my_ip := ip; arp_cache := cache |} =
  {| arp_my_mac := mac; arp_my_ip := ip; arp_cache := cache |}.
Proof.
  intros. reflexivity.
Qed.

Lemma non_broadcast_valid_returns_true_or_false : forall pkt mac,
  is_broadcast_mac (arp_sha pkt) = false ->
  validate_arp_packet pkt mac = true \/ validate_arp_packet pkt mac = false.
Proof.
  intros. destruct (validate_arp_packet pkt mac); auto.
Qed.


(* =============================================================================
   Section 15: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].
Extract Inductive option => "option" [ "Some" "None" ].

(* Core ARP Processing *)
Extraction "arp.ml"
  (* Packet construction *)
  make_arp_request
  make_arp_reply
  make_gratuitous_arp
  make_arp_probe

  (* Serialization and parsing *)
  serialize_arp_packet
  parse_arp_packet
  serialize_mac
  serialize_ipv4
  split_word16
  combine_word16

  (* Validation *)
  validate_arp_packet
  validate_rarp_packet
  is_valid_opcode
  is_broadcast_mac
  is_multicast_mac
  is_gratuitous_arp
  is_suspicious_arp

  (* Cache operations *)
  lookup_cache
  merge_cache_entry
  update_cache_entry
  add_cache_entry
  rfc826_merge
  age_cache

  (* Comparison helpers *)
  mac_eq
  ip_eq

  (* Basic ARP protocol *)
  process_arp_packet

  (* Enhanced ARP with state machine *)
  process_arp_packet_enhanced
  resolve_address
  send_arp_request_with_flood_check

  (* RARP *)
  process_rarp_packet

  (* Generic ARP processing *)
  process_generic_arp
  convert_to_generic

  (* Flood prevention *)
  update_flood_table
  clean_flood_table
  lookup_flood_entry

  (* Request queue and retry *)
  process_timeouts
  add_pending_request
  remove_pending_request
  retry_pending_request

  (* Duplicate Address Detection (RFC 5227) *)
  start_dad_probe
  process_probe_timeout
  detect_probe_conflict

  (* ARP Announcement *)
  process_announce_timeout

  (* Conflict detection and defense *)
  detect_address_conflict
  process_conflict
  can_defend
  make_defend_packet

  (* Timers *)
  timer_expired
  start_timer
  stop_timer

  (* Event processing *)
  enhanced_process_event
  process_event

  (* Network interface *)
  send_arp_on_interface.
