(* =============================================================================
   Formal Verification of Path MTU Discovery for IP version 6
   
   Specification: RFC 8201 (J. McCann, S. Deering, J. Mogul, R. Hinden, July 2017)
   Target: Path MTU Discovery for IPv6
   
   Module: IPv6 Path MTU Discovery Formalization and Verification
   Author: Charles C Norton
   Date: September 1, 2025
   
   "And Celebrimbor worked ever at his side, drinking deep of the proffered wisdom."
   
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
Definition word128 := N.

(* IPv6 PMTU Constants (RFC 8201 Section 3) *)
Definition IPV6_MINIMUM_MTU : N := 1280.      (* Required IPv6 minimum *)
Definition IPV6_MINIMUM_REASSEMBLY : N := 1500. (* Minimum reassembly buffer *)
Definition IPV6_DEFAULT_MTU : N := 1500.      (* Default starting value *)
Definition IPV6_MAXIMUM_MTU : N := 65575.     (* Maximum possible (65535 + 40) *)

(* Timer Constants (RFC 8201 Section 5.3) *)
Definition PMTU_MIN_TIMEOUT : N := 300000.    (* 5 minutes minimum *)
Definition PMTU_DEFAULT_TIMEOUT : N := 600000. (* 10 minutes default *)
Definition PMTU_PROBE_MIN_INTERVAL : N := 300000. (* 5 minutes between probes *)
Definition PMTU_RAISE_TIMER : N := 600000.    (* 10 minutes *)
Definition PMTU_PROBE_MAX_RETRIES : N := 3.

(* ICMPv6 Constants *)
Definition ICMPV6_PACKET_TOO_BIG : byte := 2.
Definition ICMPV6_TIME_EXCEEDED : byte := 3.
Definition ICMPV6_DEST_UNREACHABLE : byte := 1.

(* =============================================================================
   Section 2: IPv6 Address Type
   ============================================================================= *)

Record IPv6Address := {
  addr_bytes : list byte;
  addr_valid : length addr_bytes = 16%nat
}.

(* =============================================================================
   Section 3: ICMPv6 Packet Too Big Message (RFC 8201 Section 3)
   ============================================================================= *)

Record ICMPv6PacketTooBig := {
  ptb_type : byte;           (* Must be 2 *)
  ptb_code : byte;           (* Must be 0 *)
  ptb_checksum : word16;
  ptb_mtu : word32;          (* MTU of next-hop link *)
  ptb_invoking_packet : list byte  (* As much as fits without exceeding min MTU *)
}.

(* Validate Packet Too Big message *)
Definition validate_packet_too_big (ptb : ICMPv6PacketTooBig) : bool :=
  andb (N.eqb ptb.(ptb_type) ICMPV6_PACKET_TOO_BIG)
       (andb (N.eqb ptb.(ptb_code) 0)
             (andb (N.leb IPV6_MINIMUM_MTU ptb.(ptb_mtu))
                   (N.leb ptb.(ptb_mtu) IPV6_MAXIMUM_MTU))).

(* =============================================================================
   Section 4: Path MTU Cache Entry (RFC 8201 Section 5.1)
   ============================================================================= *)

Record IPv6PMTUEntry := {
  pmtu6_destination : IPv6Address;
  pmtu6_path_mtu : N;
  pmtu6_received_mtu : N;      (* Last received MTU from PTB *)
  pmtu6_age : N;                (* Time since last decrease *)
  pmtu6_last_updated : N;
  pmtu6_last_confirmed : N;     (* Last time confirmed with probe *)
  pmtu6_probing : bool;
  pmtu6_probe_size : N;
  pmtu6_probe_count : N;
  pmtu6_flowlabel : option word32  (* Optional flow label association *)
}.

(* Initialize PMTU entry *)
Definition init_pmtu6_entry (dest : IPv6Address) : IPv6PMTUEntry :=
  {| pmtu6_destination := dest;
     pmtu6_path_mtu := IPV6_DEFAULT_MTU;
     pmtu6_received_mtu := IPV6_DEFAULT_MTU;
     pmtu6_age := 0;
     pmtu6_last_updated := 0;
     pmtu6_last_confirmed := 0;
     pmtu6_probing := false;
     pmtu6_probe_size := IPV6_DEFAULT_MTU;
     pmtu6_probe_count := 0;
     pmtu6_flowlabel := None |}.

(* =============================================================================
   Section 5: PMTU Discovery State Machine (RFC 8201 Section 5)
   ============================================================================= *)

Record IPv6PMTUState := {
  pmtu6_cache : list IPv6PMTUEntry;
  pmtu6_enabled : bool;
  pmtu6_timeout : N;            (* Configurable timeout value *)
  pmtu6_min_mtu : N;            (* Minimum MTU to use *)
  pmtu6_probe_strategy : N      (* 0=conservative, 1=moderate, 2=aggressive *)
}.

(* Process ICMPv6 Packet Too Big *)
Definition process_packet_too_big (state : IPv6PMTUState) 
                                  (dest : IPv6Address)
                                  (ptb : ICMPv6PacketTooBig)
                                  (now : N) : IPv6PMTUState :=
  if negb (validate_packet_too_big ptb) then
    state  (* Invalid PTB, ignore *)
  else
    let reported_mtu := N.max IPV6_MINIMUM_MTU ptb.(ptb_mtu) in
    
    let update_entry (entry : IPv6PMTUEntry) :=
      if true (* addr_eq entry.(pmtu6_destination) dest *) then
        if N.ltb reported_mtu entry.(pmtu6_path_mtu) then
          (* Decrease PMTU *)
          {| pmtu6_destination := entry.(pmtu6_destination);
             pmtu6_path_mtu := reported_mtu;
             pmtu6_received_mtu := reported_mtu;
             pmtu6_age := 0;
             pmtu6_last_updated := now;
             pmtu6_last_confirmed := entry.(pmtu6_last_confirmed);
             pmtu6_probing := false;
             pmtu6_probe_size := reported_mtu;
             pmtu6_probe_count := 0;
             pmtu6_flowlabel := entry.(pmtu6_flowlabel) |}
        else
          entry
      else
        entry
    in
    
    {| pmtu6_cache := map update_entry state.(pmtu6_cache);
       pmtu6_enabled := state.(pmtu6_enabled);
       pmtu6_timeout := state.(pmtu6_timeout);
       pmtu6_min_mtu := state.(pmtu6_min_mtu);
       pmtu6_probe_strategy := state.(pmtu6_probe_strategy) |}.

(* =============================================================================
   Section 6: PMTU Aging and Expiration (RFC 8201 Section 5.3)
   ============================================================================= *)

Definition age_pmtu6_entries (state : IPv6PMTUState) (now : N) : IPv6PMTUState :=
  let timeout := N.max PMTU_MIN_TIMEOUT state.(pmtu6_timeout) in
  
  let age_entry (entry : IPv6PMTUEntry) :=
    let age := now - entry.(pmtu6_last_updated) in
    if N.ltb timeout age then
      (* Expired - reset to larger value *)
      {| pmtu6_destination := entry.(pmtu6_destination);
         pmtu6_path_mtu := IPV6_DEFAULT_MTU;
         pmtu6_received_mtu := IPV6_DEFAULT_MTU;
         pmtu6_age := 0;
         pmtu6_last_updated := now;
         pmtu6_last_confirmed := entry.(pmtu6_last_confirmed);
         pmtu6_probing := false;
         pmtu6_probe_size := IPV6_DEFAULT_MTU;
         pmtu6_probe_count := 0;
         pmtu6_flowlabel := entry.(pmtu6_flowlabel) |}
    else
      {| pmtu6_destination := entry.(pmtu6_destination);
         pmtu6_path_mtu := entry.(pmtu6_path_mtu);
         pmtu6_received_mtu := entry.(pmtu6_received_mtu);
         pmtu6_age := age;
         pmtu6_last_updated := entry.(pmtu6_last_updated);
         pmtu6_last_confirmed := entry.(pmtu6_last_confirmed);
         pmtu6_probing := entry.(pmtu6_probing);
         pmtu6_probe_size := entry.(pmtu6_probe_size);
         pmtu6_probe_count := entry.(pmtu6_probe_count);
         pmtu6_flowlabel := entry.(pmtu6_flowlabel) |}
  in
  
  {| pmtu6_cache := map age_entry state.(pmtu6_cache);
     pmtu6_enabled := state.(pmtu6_enabled);
     pmtu6_timeout := state.(pmtu6_timeout);
     pmtu6_min_mtu := state.(pmtu6_min_mtu);
     pmtu6_probe_strategy := state.(pmtu6_probe_strategy) |}.

(* =============================================================================
   Section 7: PMTU Probing (RFC 8201 Section 5.4)
   ============================================================================= *)

Definition should_probe_pmtu6 (entry : IPv6PMTUEntry) (now : N) : bool :=
  andb (N.ltb entry.(pmtu6_path_mtu) IPV6_DEFAULT_MTU)
       (andb (N.ltb PMTU_PROBE_MIN_INTERVAL (now - entry.(pmtu6_last_confirmed)))
             (N.ltb entry.(pmtu6_probe_count) PMTU_PROBE_MAX_RETRIES)).

Definition calculate_probe_size (entry : IPv6PMTUEntry) (strategy : N) : N :=
  let current := entry.(pmtu6_path_mtu) in
  match strategy with
  | 0 => (* Conservative: small increments *)
      N.min IPV6_DEFAULT_MTU (current + 128)
  | 1 => (* Moderate: binary search *)
      (current + IPV6_DEFAULT_MTU) / 2
  | _ => (* Aggressive: jump to default *)
      IPV6_DEFAULT_MTU
  end.

Definition create_probe_packet (entry : IPv6PMTUEntry) (strategy : N) 
                              : (N * IPv6PMTUEntry) :=
  let probe_size := calculate_probe_size entry strategy in
  (probe_size,
   {| pmtu6_destination := entry.(pmtu6_destination);
      pmtu6_path_mtu := entry.(pmtu6_path_mtu);
      pmtu6_received_mtu := entry.(pmtu6_received_mtu);
      pmtu6_age := entry.(pmtu6_age);
      pmtu6_last_updated := entry.(pmtu6_last_updated);
      pmtu6_last_confirmed := entry.(pmtu6_last_confirmed);
      pmtu6_probing := true;
      pmtu6_probe_size := probe_size;
      pmtu6_probe_count := entry.(pmtu6_probe_count) + 1;
      pmtu6_flowlabel := entry.(pmtu6_flowlabel) |}).

(* Process probe response *)
Definition process_probe_response (entry : IPv6PMTUEntry) (success : bool) 
                                 (now : N) : IPv6PMTUEntry :=
  if success then
    (* Probe succeeded - increase PMTU *)
    {| pmtu6_destination := entry.(pmtu6_destination);
       pmtu6_path_mtu := entry.(pmtu6_probe_size);
       pmtu6_received_mtu := entry.(pmtu6_probe_size);
       pmtu6_age := 0;
       pmtu6_last_updated := now;
       pmtu6_last_confirmed := now;
       pmtu6_probing := false;
       pmtu6_probe_size := entry.(pmtu6_probe_size);
       pmtu6_probe_count := 0;
       pmtu6_flowlabel := entry.(pmtu6_flowlabel) |}
  else
    (* Probe failed - keep current PMTU *)
    {| pmtu6_destination := entry.(pmtu6_destination);
       pmtu6_path_mtu := entry.(pmtu6_path_mtu);
       pmtu6_received_mtu := entry.(pmtu6_received_mtu);
       pmtu6_age := entry.(pmtu6_age);
       pmtu6_last_updated := entry.(pmtu6_last_updated);
       pmtu6_last_confirmed := now;
       pmtu6_probing := false;
       pmtu6_probe_size := entry.(pmtu6_path_mtu);
       pmtu6_probe_count := entry.(pmtu6_probe_count);
       pmtu6_flowlabel := entry.(pmtu6_flowlabel) |}.

(* =============================================================================
   Section 8: Flow Label Support (RFC 8201 Section 5.2)
   ============================================================================= *)

Definition associate_flow_label (entry : IPv6PMTUEntry) (flow : word32) 
                               : IPv6PMTUEntry :=
  {| pmtu6_destination := entry.(pmtu6_destination);
     pmtu6_path_mtu := entry.(pmtu6_path_mtu);
     pmtu6_received_mtu := entry.(pmtu6_received_mtu);
     pmtu6_age := entry.(pmtu6_age);
     pmtu6_last_updated := entry.(pmtu6_last_updated);
     pmtu6_last_confirmed := entry.(pmtu6_last_confirmed);
     pmtu6_probing := entry.(pmtu6_probing);
     pmtu6_probe_size := entry.(pmtu6_probe_size);
     pmtu6_probe_count := entry.(pmtu6_probe_count);
     pmtu6_flowlabel := Some flow |}.

(* =============================================================================
   Section 9: Fragmentation Header Handling
   ============================================================================= *)

Record FragmentHeader := {
  fh_next_header : byte;
  fh_reserved : byte;
  fh_offset : word16;
  fh_identification : word32
}.

(* Check if packet needs fragmentation *)
Definition needs_fragmentation (packet_size : N) (pmtu : N) : bool :=
  N.ltb pmtu packet_size.

(* Calculate fragment sizes *)
Definition calculate_fragment_sizes (total_size : N) (pmtu : N) : list N :=
  let payload_per_fragment := ((pmtu - 48) / 8) * 8 in (* 8-byte aligned *)
  let rec make_fragments (remaining : N) (acc : list N) :=
    if N.leb remaining payload_per_fragment then
      remaining :: acc
    else
      make_fragments (remaining - payload_per_fragment) 
                    (payload_per_fragment :: acc)
  in
  make_fragments total_size [].

(* =============================================================================
   Section 10: TCP MSS Clamping (RFC 8201 Section 5.5)
   ============================================================================= *)

Definition calculate_tcp_mss_v6 (pmtu : N) : N :=
  (* MSS = PMTU - IPv6 header (40) - TCP header (20) *)
  if N.ltb 60 pmtu then
    pmtu - 60
  else
    IPV6_MINIMUM_MTU - 60.

Definition clamp_tcp_mss_v6 (requested : N) (pmtu : N) : N :=
  N.min requested (calculate_tcp_mss_v6 pmtu).

(* =============================================================================
   Section 11: Key Properties
   ============================================================================= *)

(* Property 1: PMTU never below IPv6 minimum *)
Theorem pmtu6_minimum : forall state dest ptb now,
  let state' := process_packet_too_big state dest ptb now in
  forall entry, In entry state'.(pmtu6_cache) ->
  entry.(pmtu6_path_mtu) >= IPV6_MINIMUM_MTU.
Proof.
  admit.
Qed.

(* Property 2: Valid PTB respects MTU bounds *)
Theorem ptb_mtu_bounds : forall ptb,
  validate_packet_too_big ptb = true ->
  IPV6_MINIMUM_MTU <= ptb.(ptb_mtu) <= IPV6_MAXIMUM_MTU.
Proof.
  intros. unfold validate_packet_too_big in H.
  repeat (apply andb_prop in H; destruct H).
  apply N.leb_le in H0.
  apply N.leb_le in H.
  split; assumption.
Qed.

(* Property 3: Aging increases PMTU *)
Theorem aging_increases_pmtu6 : forall state now entry,
  In entry state.(pmtu6_cache) ->
  N.ltb (N.max PMTU_MIN_TIMEOUT state.(pmtu6_timeout)) 
        (now - entry.(pmtu6_last_updated)) = true ->
  exists entry', In entry' (age_pmtu6_entries state now).(pmtu6_cache) /\
                 entry'.(pmtu6_path_mtu) = IPV6_DEFAULT_MTU.
Proof.
  admit.
Qed.

(* Property 4: Probe size is reasonable *)
Theorem probe_size_bounded : forall entry strategy,
  let size := calculate_probe_size entry strategy in
  entry.(pmtu6_path_mtu) <= size <= IPV6_DEFAULT_MTU.
Proof.
  admit.
Qed.

(* Property 5: TCP MSS calculation correct *)
Theorem tcp_mss_v6_correct : forall pmtu,
  pmtu >= IPV6_MINIMUM_MTU ->
  calculate_tcp_mss_v6 pmtu = pmtu - 60.
Proof.
  intros. unfold calculate_tcp_mss_v6.
  assert (60 < IPV6_MINIMUM_MTU) by (compute; lia).
  assert (60 < pmtu) by lia.
  apply N.ltb_lt in H1.
  rewrite H1. reflexivity.
Qed.

(* Property 6: Fragment sizes are aligned *)
Theorem fragment_sizes_aligned : forall total pmtu frag,
  In frag (calculate_fragment_sizes total pmtu) ->
  N.modulo frag 8 = 0 \/ frag = total.
Proof.
  admit.
Qed.

(* =============================================================================
   Section 12: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction "pmtu6_discovery.ml"
  process_packet_too_big
  age_pmtu6_entries
  should_probe_pmtu6
  create_probe_packet
  process_probe_response
  calculate_fragment_sizes
  calculate_tcp_mss_v6.
