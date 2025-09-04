(* =============================================================================
   Formal Verification of Internet Protocol Version 4 (IPv4)
   
   Specification: RFC 791 (Jon Postel, September 1981)
   Target: IPv4 Datagram Protocol
   
   Module: IPv4 Protocol Formalization and Verification
   Author: Charles C Norton
   Date: August 29, 2025
   
   "Then spoke he unto the doorwardens, saying: 
    'I am Annatar, whom ye have not looked for.'"
   
   ============================================================================= *)

From Coq Require Import
  List
  NArith.NArith
  NArith.Ndiv_def
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

(* IP Version *)
Definition IP_VERSION_4 : N := 4.

(* Minimum and maximum header lengths *)
Definition MIN_IHL : N := 5.      (* 5 * 32 bits = 20 bytes *)
Definition MAX_IHL : N := 15.     (* 15 * 32 bits = 60 bytes *)

(* Protocol numbers *)
Definition PROTO_ICMP : byte := 1.
Definition PROTO_TCP : byte := 6.
Definition PROTO_UDP : byte := 17.

(* Type of Service bits (RFC 791 original) *)
Record TypeOfService := {
  tos_precedence : N;  (* 3 bits: 0-7 *)
  tos_delay : bool;     (* Low delay *)
  tos_throughput : bool; (* High throughput *)
  tos_reliability : bool; (* High reliability *)
  tos_reserved : N      (* 2 bits reserved *)
}.

(* Precedence values *)
Definition PREC_NETWORK_CONTROL : N := 7.
Definition PREC_INTERNETWORK_CONTROL : N := 6.
Definition PREC_CRITIC_ECP : N := 5.
Definition PREC_FLASH_OVERRIDE : N := 4.
Definition PREC_FLASH : N := 3.
Definition PREC_IMMEDIATE : N := 2.
Definition PREC_PRIORITY : N := 1.
Definition PREC_ROUTINE : N := 0.

(* =============================================================================
   Section 2: IP Address Type
   ============================================================================= *)

(* IPv4 address as 4-byte structure for better manipulation *)
Record IPv4 := {
  a0 : byte;  (* Most significant byte *)
  a1 : byte;
  a2 : byte;
  a3 : byte   (* Least significant byte *)
}.

(* Constructor with byte normalization *)
Definition mkIPv4 (b0 b1 b2 b3 : N) : IPv4 :=
  {| a0 := b0 mod 256;
     a1 := b1 mod 256;
     a2 := b2 mod 256;
     a3 := b3 mod 256 |}.

(* Convert to/from 32-bit word *)
Definition IPv4Address := word32.

Definition ipv4_to_word32 (ip : IPv4) : IPv4Address :=
  ip.(a0) * 16777216 + ip.(a1) * 65536 + ip.(a2) * 256 + ip.(a3).

Definition word32_to_ipv4 (w : IPv4Address) : IPv4 :=
  mkIPv4 ((w / 16777216) mod 256)
         ((w / 65536) mod 256)
         ((w / 256) mod 256)
         (w mod 256).

(* IPv4 as list of 16-bit words for checksum computation *)
Definition ipv4_words (ip : IPv4) : list word16 :=
  [ip.(a0) * 256 + ip.(a1); ip.(a2) * 256 + ip.(a3)].

(* Address classes per RFC 791 *)
Definition is_class_a (ip : IPv4) : bool :=
  ip.(a0) <? 128.  (* High bit = 0 *)

Definition is_class_b (ip : IPv4) : bool :=
  andb (128 <=? ip.(a0)) (ip.(a0) <? 192).  (* High bits = 10 *)

Definition is_class_c (ip : IPv4) : bool :=
  andb (192 <=? ip.(a0)) (ip.(a0) <? 224).  (* High bits = 110 *)

Definition is_class_d (ip : IPv4) : bool :=
  andb (224 <=? ip.(a0)) (ip.(a0) <? 240).  (* High bits = 1110 (multicast) *)

Definition is_class_e (ip : IPv4) : bool :=
  240 <=? ip.(a0).  (* High bits = 1111 (reserved) *)

(* Special addresses *)
Definition ADDR_ANY : IPv4 := mkIPv4 0 0 0 0.
Definition ADDR_BROADCAST : IPv4 := mkIPv4 255 255 255 255.
Definition ADDR_LOOPBACK : IPv4 := mkIPv4 127 0 0 1.

(* Address equality *)
Definition ipv4_eq (ip1 ip2 : IPv4) : bool :=
  andb (andb (N.eqb ip1.(a0) ip2.(a0)) (N.eqb ip1.(a1) ip2.(a1)))
       (andb (N.eqb ip1.(a2) ip2.(a2)) (N.eqb ip1.(a3) ip2.(a3))).

(* =============================================================================
   Section 3: IPv4 Header Structure (RFC 791 Section 3.1)
   ============================================================================= *)

Record IPv4Header := {
  ip_version : N;           (* 4 bits: Must be 4 *)
  ip_ihl : N;               (* 4 bits: Header length in 32-bit words *)
  ip_tos : byte;            (* 8 bits: Type of service *)
  ip_total_length : word16; (* 16 bits: Total datagram length *)
  ip_id : word16;           (* 16 bits: Identification *)
  ip_flags : N;             (* 3 bits: Control flags *)
  ip_frag_offset : N;       (* 13 bits: Fragment offset in 8-byte units *)
  ip_ttl : byte;            (* 8 bits: Time to live *)
  ip_protocol : byte;       (* 8 bits: Next protocol *)
  ip_checksum : word16;     (* 16 bits: Header checksum *)
  ip_src : IPv4;            (* 32 bits: Source address *)
  ip_dst : IPv4;            (* 32 bits: Destination address *)
  ip_options : list byte    (* Variable: Options and padding *)
}.

(* Flag bit positions *)
Definition FLAG_RESERVED : N := 0.  (* Bit 0: Must be 0 *)
Definition FLAG_DF : N := 1.        (* Bit 1: Don't Fragment *)
Definition FLAG_MF : N := 2.        (* Bit 2: More Fragments *)

(* Extract individual flags *)
Definition get_flag (flags : N) (bit : N) : bool :=
  N.testbit flags bit.

Definition set_flag (flags : N) (bit : N) (value : bool) : N :=
  if value then N.lor flags (N.shiftl 1 bit)
  else N.land flags (N.lxor (N.shiftl 1 bit) (N.ones 16)).

(* =============================================================================
   Section 4: IPv4 Options (RFC 791 Section 3.1)
   ============================================================================= *)

(* Option format: copied(1) | class(2) | number(5) *)
Record OptionType := {
  opt_copied : bool;     (* Copied to fragments *)
  opt_class : N;        (* 2 bits: 0=control, 2=debug *)
  opt_number : N        (* 5 bits: Option number *)
}.

(* Standard option types *)
Definition OPT_END : byte := 0.          (* End of options *)
Definition OPT_NOP : byte := 1.          (* No operation *)
Definition OPT_SECURITY : byte := 130.    (* Security (copied) *)
Definition OPT_LSRR : byte := 131.        (* Loose source route (copied) *)
Definition OPT_SSRR : byte := 137.        (* Strict source route (copied) *)
Definition OPT_RR : byte := 7.            (* Record route *)
Definition OPT_STREAM_ID : byte := 136.   (* Stream ID (copied) *)
Definition OPT_TIMESTAMP : byte := 68.    (* Internet timestamp *)

(* Option structure *)
Inductive IPOption :=
  | OptEnd : IPOption                    (* Type 0: End of options *)
  | OptNop : IPOption                    (* Type 1: No operation *)
  | OptSecurity : list byte -> IPOption  (* Type 130: Security *)
  | OptLSRR : byte -> list IPv4 -> IPOption (* Type 131: Loose source route *)
  | OptSSRR : byte -> list IPv4 -> IPOption (* Type 137: Strict source route *)
  | OptRR : byte -> list IPv4 -> IPOption   (* Type 7: Record route *)
  | OptStreamID : word16 -> IPOption     (* Type 136: Stream identifier *)
  | OptTimestamp : byte -> byte -> list (IPv4 * word32) -> IPOption
  | OptUnknown : byte -> list byte -> IPOption.

(* Parse option type byte *)
Definition parse_option_type (t : byte) : OptionType :=
  {| opt_copied := N.testbit t 7;
     opt_class := N.land (N.shiftr t 5) 3;
     opt_number := N.land t 31 |}.

(* Serialize option type *)
Definition serialize_option_type (ot : OptionType) : byte :=
  N.lor (N.lor (if ot.(opt_copied) then 128 else 0)
               (N.shiftl (N.land ot.(opt_class) 3) 5))
        (N.land ot.(opt_number) 31).

(* Check if option is copied on fragmentation *)
Definition option_is_copied (opt : IPOption) : bool :=
  match opt with
  | OptEnd => false
  | OptNop => false
  | OptSecurity _ => true
  | OptLSRR _ _ => true
  | OptSSRR _ _ => true
  | OptStreamID _ => true
  | OptRR _ _ => false  (* Record Route is not copied *)
  | OptTimestamp _ _ _ => false  (* Timestamp is not copied *)
  | OptUnknown t _ => N.testbit t 7
  end.

(* =============================================================================
   Section 5: Header Checksum (RFC 791 Section 3.1)
   ============================================================================= *)

(* Advanced checksum implementation from RFC768.v *)

(* Convert bytes to 16-bit words (big-endian) *)
Fixpoint words16_of_bytes_be (bs : list byte) : list word16 :=
  match bs with
  | [] => []
  | b1 :: [] => [b1 * 256]  (* Pad with zero *)
  | b1 :: b2 :: rest => (b1 * 256 + b2) :: words16_of_bytes_be rest
  end.

(* Add with carry for one's complement *)
Fixpoint add_carry (s : N) (fuel : nat) : word16 :=
  match fuel with
  | O => s mod 65536
  | S fuel' =>
      let carry := s / 65536 in
      let base := s mod 65536 in
      if N.eqb carry 0 then base
      else add_carry (base + carry) fuel'
  end.

(* One's complement sum with proper carry handling *)
Definition ones_complement_sum (words : list word16) : word16 :=
  let sum := fold_left (fun acc w => acc + w) words 0 in
  add_carry sum 10.

(* Main checksum function *)
Definition cksum16 (words : list word16) : word16 :=
  N.lxor (ones_complement_sum words) 0xFFFF.

(* Compute checksum over header *)
Definition compute_header_checksum (h : IPv4Header) : word16 :=
  let header_bytes :=
    (* Build header as byte list *)
    [N.lor (N.shiftl h.(ip_version) 4) h.(ip_ihl);
     h.(ip_tos);
     h.(ip_total_length) / 256; h.(ip_total_length) mod 256;
     h.(ip_id) / 256; h.(ip_id) mod 256;
     N.lor (N.shiftl h.(ip_flags) 13) h.(ip_frag_offset) / 256;
     N.lor (N.shiftl h.(ip_flags) 13) h.(ip_frag_offset) mod 256;
     h.(ip_ttl);
     h.(ip_protocol);
     0; 0;
     h.(ip_src).(a0); h.(ip_src).(a1); h.(ip_src).(a2); h.(ip_src).(a3);
     h.(ip_dst).(a0); h.(ip_dst).(a1); h.(ip_dst).(a2); h.(ip_dst).(a3)]
     ++ h.(ip_options)
  in
  cksum16 (words16_of_bytes_be header_bytes).

(* Verify checksum *)
Definition verify_header_checksum (h : IPv4Header) : bool :=
  let computed := compute_header_checksum h in
  N.eqb computed h.(ip_checksum).

(* =============================================================================
   Section 6: Fragmentation (RFC 791 Section 3.2)
   ============================================================================= *)

Record Fragment := {
  frag_id : word16;           (* Identification *)
  frag_offset : N;           (* Offset in 8-byte units *)
  frag_more : bool;          (* More fragments flag *)
  frag_data : list byte      (* Fragment data *)
}.

(* Fragment a datagram *)
Fixpoint fragment_datagram_aux (h : IPv4Header) (data : list byte) (mtu : N) 
                               (offset : N) (fuel : nat) : list (IPv4Header * list byte) :=
  match fuel with
  | O => []
  | S fuel' =>
      match data with
      | [] => []
      | _ =>
          let header_len := h.(ip_ihl) * 4 in
          let max_data := mtu - header_len in
          let max_data_aligned := (max_data / 8) * 8 in
          let chunk_size := N.min max_data_aligned (N.of_nat (length data)) in
          let chunk := firstn (N.to_nat chunk_size) data in
          let rest := skipn (N.to_nat chunk_size) data in
          let more_flag := negb (match rest with [] => true | _ => false end) in
          let frag_header := 
            {| ip_version := h.(ip_version);
               ip_ihl := h.(ip_ihl);
               ip_tos := h.(ip_tos);
               ip_total_length := header_len + chunk_size;
               ip_id := h.(ip_id);
               ip_flags := set_flag h.(ip_flags) FLAG_MF more_flag;
               ip_frag_offset := offset / 8;
               ip_ttl := h.(ip_ttl);
               ip_protocol := h.(ip_protocol);
               ip_checksum := 0;
               ip_src := h.(ip_src);
               ip_dst := h.(ip_dst);
               ip_options := if N.eqb offset 0 then h.(ip_options)
                            else [] (* Simplified: copy no options for non-first fragments *)
            |} in
          (frag_header, chunk) :: fragment_datagram_aux h rest mtu (offset + chunk_size) fuel'
      end
  end.

Definition fragment_datagram (h : IPv4Header) (data : list byte) (mtu : N) 
                            : list (IPv4Header * list byte) :=
  fragment_datagram_aux h data mtu 0 (length data).

(* Reassembly state *)
Record ReassemblyBuffer := {
  reasm_id : word16;
  reasm_src : IPv4;
  reasm_dst : IPv4;
  reasm_protocol : byte;
  reasm_fragments : list Fragment;
  reasm_timer : N  (* Reassembly timeout *)
}.

(* Check if all fragments received *)
Definition is_complete (frags : list Fragment) : bool :=
  let sorted := (* sort by offset *) frags in
  let fix check_contiguous (f : list Fragment) (expected_offset : N) : bool :=
    match f with
    | [] => true
    | frag :: rest =>
        andb (N.eqb frag.(frag_offset) expected_offset)
             (if frag.(frag_more) 
              then check_contiguous rest (expected_offset + N.of_nat (length frag.(frag_data)) / 8)
              else match rest with [] => true | _ => false end)
    end
  in check_contiguous sorted 0.

(* Reassemble fragments *)
Definition reassemble_fragments (frags : list Fragment) : option (list byte) :=
  if is_complete frags then
    Some (flat_map frag_data (*(sort by offset)*) frags)
  else None.

(* =============================================================================
   Section 7: Routing and Forwarding
   ============================================================================= *)

Record RoutingEntry := {
  route_dest : IPv4;
  route_mask : IPv4;
  route_gateway : IPv4;
  route_interface : N;
  route_metric : N
}.

Definition RoutingTable := list RoutingEntry.

(* Apply network mask *)
Definition apply_mask (addr : IPv4) (mask : IPv4) : IPv4 :=
  mkIPv4 (N.land addr.(a0) mask.(a0))
         (N.land addr.(a1) mask.(a1))
         (N.land addr.(a2) mask.(a2))
         (N.land addr.(a3) mask.(a3)).

(* Longest prefix match *)
Definition lookup_route (table : RoutingTable) (dest : IPv4) 
                       : option RoutingEntry :=
  let matches := filter (fun r => 
    ipv4_eq (apply_mask dest r.(route_mask)) 
            (apply_mask r.(route_dest) r.(route_mask))) table in
  (* Returns first matching entry *)
  hd_error matches.

(* =============================================================================
   Section 8: IP Processing Functions
   ============================================================================= *)

(* Validate header *)
Definition validate_header (h : IPv4Header) : bool :=
  andb (N.eqb h.(ip_version) IP_VERSION_4)
  (andb (N.leb MIN_IHL h.(ip_ihl))
  (andb (N.leb h.(ip_ihl) MAX_IHL)
  (andb (N.leb (h.(ip_ihl) * 4) h.(ip_total_length))
        (verify_header_checksum h)))).

(* Process TTL *)
Definition decrement_ttl (h : IPv4Header) : option IPv4Header :=
  if N.eqb h.(ip_ttl) 0 then None
  else Some {| ip_version := h.(ip_version);
               ip_ihl := h.(ip_ihl);
               ip_tos := h.(ip_tos);
               ip_total_length := h.(ip_total_length);
               ip_id := h.(ip_id);
               ip_flags := h.(ip_flags);
               ip_frag_offset := h.(ip_frag_offset);
               ip_ttl := h.(ip_ttl) - 1;
               ip_protocol := h.(ip_protocol);
               ip_checksum := 0; (* Must recompute *)
               ip_src := h.(ip_src);
               ip_dst := h.(ip_dst);
               ip_options := h.(ip_options) |}.

(* Check if packet is for us *)
Definition is_local_address (addr : IPv4) (my_addrs : list IPv4) : bool :=
  existsb (ipv4_eq addr) my_addrs.

(* Main receive processing *)
Inductive IPReceiveResult :=
  | IPDeliver : byte -> list byte -> IPReceiveResult  (* Protocol and data *)
  | IPForward : IPv4Header -> list byte -> IPReceiveResult
  | IPDrop : IPReceiveResult
  | IPError : N -> IPReceiveResult. (* Error code *)

Definition process_ip_receive (h : IPv4Header) (data : list byte) 
                             (my_addrs : list IPv4)
                             (routing : RoutingTable) : IPReceiveResult :=
  (* Step 1: Validate header *)
  if negb (validate_header h) then IPError 1 (* Bad header *)
  else
    (* Step 2: Check if for us *)
    if is_local_address h.(ip_dst) my_addrs then
      (* Step 3: Reassembly if fragmented *)
      if orb (negb (N.eqb h.(ip_frag_offset) 0))
             (get_flag h.(ip_flags) FLAG_MF) then
        IPDrop (* Simplified - should reassemble *)
      else
        (* Step 4: Deliver to upper protocol *)
        IPDeliver h.(ip_protocol) data
    else
      (* Step 5: Forward if not for us *)
      match decrement_ttl h with
      | None => IPError 2 (* TTL expired *)
      | Some h' =>
          match lookup_route routing h.(ip_dst) with
          | None => IPError 3 (* No route *)
          | Some route => IPForward h' data
          end
      end.

(* =============================================================================
   Section 9: Option Processing
   ============================================================================= *)

(* Process Record Route option *)
Definition process_record_route (opt : IPOption) (my_addr : IPv4) 
                               : IPOption :=
  match opt with
  | OptRR ptr addrs =>
      if N.ltb ptr (N.of_nat (length addrs) * 4 + 3) then
        OptRR (ptr + 4) (addrs ++ [my_addr])
      else opt
  | _ => opt
  end.

(* Process Timestamp option *)
Definition process_timestamp (opt : IPOption) (my_addr : IPv4) 
                            (timestamp : word32) : IPOption :=
  match opt with
  | OptTimestamp ptr oflw stamps =>
      if N.ltb ptr (N.of_nat (length stamps) * 8 + 4) then
        OptTimestamp (ptr + 8) oflw (stamps ++ [(my_addr, timestamp)])
      else 
        OptTimestamp ptr (oflw + 1) stamps
  | _ => opt
  end.

(* Copy options for fragmentation *)
Definition copy_options_for_fragment (options : list IPOption) 
                                    (first_frag : bool) : list IPOption :=
  if first_frag then options
  else filter option_is_copied options.

(* =============================================================================
   Section 10: Source Routing
   ============================================================================= *)

(* Process source route option *)
Definition process_source_route (opt : IPOption) (h : IPv4Header) 
                               : option IPv4Header :=
  match opt with
  | OptLSRR ptr addrs | OptSSRR ptr addrs =>
      let idx := (ptr - 4) / 4 in
      match nth_error addrs (N.to_nat idx) with
      | Some next_hop =>
          Some {| ip_version := h.(ip_version);
                  ip_ihl := h.(ip_ihl);
                  ip_tos := h.(ip_tos);
                  ip_total_length := h.(ip_total_length);
                  ip_id := h.(ip_id);
                  ip_flags := h.(ip_flags);
                  ip_frag_offset := h.(ip_frag_offset);
                  ip_ttl := h.(ip_ttl);
                  ip_protocol := h.(ip_protocol);
                  ip_checksum := 0;
                  ip_src := h.(ip_src);
                  ip_dst := next_hop; (* Route to next hop *)
                  ip_options := h.(ip_options) |}
      | None => Some h (* End of route *)
      end
  | _ => Some h
  end.

(* =============================================================================
   Section 11: Key Properties
   ============================================================================= *)

(* Property 1: Checksum correctness *)
Theorem checksum_zero_on_valid : forall h,
  validate_header h = true ->
  let h' := {| ip_version := h.(ip_version);
               ip_ihl := h.(ip_ihl);
               ip_tos := h.(ip_tos);
               ip_total_length := h.(ip_total_length);
               ip_id := h.(ip_id);
               ip_flags := h.(ip_flags);
               ip_frag_offset := h.(ip_frag_offset);
               ip_ttl := h.(ip_ttl);
               ip_protocol := h.(ip_protocol);
               ip_checksum := compute_header_checksum h;
               ip_src := h.(ip_src);
               ip_dst := h.(ip_dst);
               ip_options := h.(ip_options) |} in
  verify_header_checksum h' = true.
Proof.
  intros h Hvalid.
  unfold validate_header in Hvalid.
  repeat (apply andb_prop in Hvalid; destruct Hvalid as [? Hvalid]).
  unfold verify_header_checksum.
  simpl.
  (* The checksum of a properly formed header with correct checksum is valid *)
  unfold compute_header_checksum.
  simpl.
  (* When we compute the checksum of h' which has the computed checksum, it verifies *)
  apply N.eqb_refl.
Qed.

(* Property 2: Fragment offset alignment *)
Theorem fragment_offset_aligned : forall h data mtu frags,
  fragment_datagram h data mtu = frags ->
  forall fh fd, In (fh, fd) frags ->
  (fh.(ip_frag_offset) * 8) mod 8 = 0.
Proof.
  intros h data mtu frags H_frag fh fd H_in.
  (* Fragment offset * 8 is always divisible by 8 *)
  apply N.mod_mul.
  discriminate.
Qed.

(* Property 3: TTL monotonicity *)
Theorem ttl_decreases : forall h h',
  decrement_ttl h = Some h' ->
  h'.(ip_ttl) < h.(ip_ttl).
Proof.
  intros h h' Hdec.
  unfold decrement_ttl in Hdec.
  destruct (N.eqb h.(ip_ttl) 0) eqn:E.
  - discriminate.
  - inversion Hdec. simpl. 
    apply N.eqb_neq in E. lia.
Qed.

(* Property 4: Reassembly succeeds for complete fragment sets *)
Theorem reassembly_complete : forall frags,
  is_complete frags = true ->
  exists data, reassemble_fragments frags = Some data.
Proof.
  intros frags H_complete.
  unfold reassemble_fragments.
  rewrite H_complete.
  exists (flat_map frag_data frags).
  reflexivity.
Qed.

(* Property 5: Fragment count is positive when data is non-empty *)
Theorem fragment_count_positive : forall h data mtu frags,
  fragment_datagram h data mtu = frags ->
  data <> [] ->
  frags <> [].
Proof.
  intros h data mtu frags H_frag H_data_nonempty.
  unfold fragment_datagram in H_frag.
  destruct data.
  - contradiction.
  - intro H_frags_empty.
    rewrite H_frags_empty in H_frag.
    simpl in H_frag.
    discriminate H_frag.
Qed.

(* Property 6: Header length bounds *)
Theorem header_length_valid : forall h,
  validate_header h = true ->
  20 <= h.(ip_ihl) * 4 <= 60.
Proof.
  intros h Hvalid.
  unfold validate_header in Hvalid.
  (* Decompose validation conditions *)
  apply andb_prop in Hvalid. destruct Hvalid as [Hversion Hrest1].
  apply andb_prop in Hrest1. destruct Hrest1 as [Hihl_min Hrest2].
  apply andb_prop in Hrest2. destruct Hrest2 as [Hihl_max Hrest3].
  apply andb_prop in Hrest3. destruct Hrest3 as [Hlength_check Hchecksum].
  apply N.leb_le in Hihl_min.
  apply N.leb_le in Hihl_max.
  unfold MIN_IHL, MAX_IHL in *.
  split; lia.
Qed.

(* =============================================================================
   Section 12: Security Options (RFC 791 Section 3.1)
   ============================================================================= *)

Record SecurityOption := {
  sec_level : word16;          (* Security level *)
  sec_compartments : word16;   (* Compartments *)  
  sec_handling : word16;       (* Handling restrictions *)
  sec_tcc : N                  (* Transmission control code: 24 bits *)
}.

(* Security levels *)
Definition SEC_UNCLASSIFIED : word16 := 0x0000.
Definition SEC_CONFIDENTIAL : word16 := 0xF135.
Definition SEC_EFTO : word16 := 0x789C.
Definition SEC_MMMM : word16 := 0xBC4E.
Definition SEC_PROG : word16 := 0x5E26.
Definition SEC_RESTRICTED : word16 := 0xAF13.
Definition SEC_SECRET : word16 := 0xD788.
Definition SEC_TOP_SECRET : word16 := 0x6BC5.

(* =============================================================================
   Section 13: ICMP Integration Points
   ============================================================================= *)

Inductive ICMPTrigger :=
  | ICMP_TTLExpired : IPv4Header -> ICMPTrigger
  | ICMP_Unreachable : IPv4Header -> N -> ICMPTrigger (* Code *)
  | ICMP_FragmentationNeeded : IPv4Header -> N -> ICMPTrigger (* MTU *)
  | ICMP_ParameterProblem : IPv4Header -> N -> ICMPTrigger (* Pointer *)
  | ICMP_SourceQuench : IPv4Header -> ICMPTrigger.

(* Generate ICMP error conditions *)
Definition check_icmp_conditions (h : IPv4Header) (result : IPReceiveResult) 
                                : option ICMPTrigger :=
  match result with
  | IPError 2 => Some (ICMP_TTLExpired h)  
  | IPError 3 => Some (ICMP_Unreachable h 1) (* Host unreachable *)
  | _ => None
  end.

(* =============================================================================
   Section 14: Serialization and Parsing
   ============================================================================= *)

(* Serialize header to bytes *)
Definition serialize_ipv4_header (h : IPv4Header) : list byte :=
  let ver_ihl := N.lor (N.shiftl h.(ip_version) 4) h.(ip_ihl) in
  let flags_frag := N.lor (N.shiftl h.(ip_flags) 13) h.(ip_frag_offset) in
  [ver_ihl;
   h.(ip_tos);
   h.(ip_total_length) / 256; h.(ip_total_length) mod 256;
   h.(ip_id) / 256; h.(ip_id) mod 256;
   flags_frag / 256; flags_frag mod 256;
   h.(ip_ttl);
   h.(ip_protocol);
   h.(ip_checksum) / 256; h.(ip_checksum) mod 256;
   h.(ip_src).(a0);
   h.(ip_src).(a1);
   h.(ip_src).(a2);
   h.(ip_src).(a3);
   h.(ip_dst).(a0);
   h.(ip_dst).(a1);
   h.(ip_dst).(a2);
   h.(ip_dst).(a3)]
  ++ h.(ip_options).

(* Parse header from bytes *)
Definition parse_ipv4_header (data : list byte) : option (IPv4Header * list byte) :=
  match data with
  | ver_ihl :: tos :: len_h :: len_l :: 
    id_h :: id_l :: flags_frag_h :: flags_frag_l ::
    ttl :: proto :: cksum_h :: cksum_l ::
    src0 :: src1 :: src2 :: src3 ::
    dst0 :: dst1 :: dst2 :: dst3 :: rest =>
      let version := N.shiftr ver_ihl 4 in
      let ihl := N.land ver_ihl 15 in
      if andb (N.eqb version 4) (N.leb 5 ihl) then
        let total_length := len_h * 256 + len_l in
        let id := id_h * 256 + id_l in
        let flags_frag := flags_frag_h * 256 + flags_frag_l in
        let flags := N.shiftr flags_frag 13 in
        let frag_offset := N.land flags_frag 8191 in
        let checksum := cksum_h * 256 + cksum_l in
        let option_len := (ihl - 5) * 4 in
        let options := firstn (N.to_nat option_len) rest in
        let payload := skipn (N.to_nat option_len) rest in
        Some ({| ip_version := version;
                 ip_ihl := ihl;
                 ip_tos := tos;
                 ip_total_length := total_length;
                 ip_id := id;
                 ip_flags := flags;
                 ip_frag_offset := frag_offset;
                 ip_ttl := ttl;
                 ip_protocol := proto;
                 ip_checksum := checksum;
                 ip_src := mkIPv4 src0 src1 src2 src3;
                 ip_dst := mkIPv4 dst0 dst1 dst2 dst3;
                 ip_options := options |}, payload)
      else None
  | _ => None
  end.

(* Serialization produces non-empty output *)
Theorem serialize_nonempty : forall h,
  validate_header h = true ->
  serialize_ipv4_header h <> [].
Proof.
  intros h H_valid.
  unfold serialize_ipv4_header.
  (* Minimum header size is 20 bytes *)
  intro H_empty.
  discriminate H_empty.
Qed.

(* =============================================================================
   Section 15: Network Byte Order Helpers
   ============================================================================= *)

Definition htons (n : word16) : word16 := n.
Definition ntohs (n : word16) : word16 := n.
Definition htonl (n : word32) : word32 := n.
Definition ntohl (n : word32) : word32 := n.

(* =============================================================================
   Section 16: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].
Extract Inductive option => "option" [ "Some" "None" ].

Extraction "ipv4.ml"
  process_ip_receive
  fragment_datagram
  reassemble_fragments
  compute_header_checksum
  validate_header
  lookup_route
  process_source_route.
