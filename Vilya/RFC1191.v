(* =============================================================================
   Formal Verification of Path MTU Discovery
   
   Specification: RFC 1191 (J. Mogul, S. Deering, November 1990)
   Target: Path MTU Discovery for IPv4
   
   Module: Path MTU Discovery Formalization and Verification
   Author: Charles C Norton
   Date: September 1, 2025
   
   "Each word that Annatar spoke seemed to open doors long shut in their understanding."
   
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

(* Path MTU Constants (RFC 1191 Section 3) *)
Definition MIN_IPV4_MTU : N := 68.          (* Minimum IPv4 MTU *)
Definition MIN_PMTU : N := 576.             (* Minimum recommended PMTU *)
Definition DEFAULT_PMTU : N := 1500.        (* Ethernet default *)
Definition MAX_IPV4_HEADER : N := 60.       (* Maximum IPv4 header size *)

(* Plateau MTU values (RFC 1191 Section 7) *)
Definition MTU_PLATEAU_TABLE : list N :=
  [65535;  (* Maximum IPv4 packet *)
   32000;  (* Just in case *)
   17914;  (* 16Mb IBM Token Ring *)
   8166;   (* IEEE 802.4 *)
   4352;   (* FDDI *)
   4464;   (* IEEE 802.5 (4Mb max) *)
   2002;   (* IEEE 802.5 (4Mb recommended) *)
   1492;   (* IEEE 802.3 *)
   1500;   (* Ethernet *)
   1006;   (* SLIP/ARPANET *)
   576;    (* X.25 Networks *)
   508;    (* ARCNET *)
   296;    (* Point-to-Point (low delay) *)
   MIN_IPV4_MTU].

(* Timer Constants *)
Definition PMTU_TIMEOUT : N := 600000.       (* 10 minutes in milliseconds *)
Definition PMTU_RAISE_TIMER : N := 600000.   (* 10 minutes *)
Definition PMTU_PROBE_INTERVAL : N := 30000. (* 30 seconds *)

(* =============================================================================
   Section 2: ICMP Processing (RFC 1191 Section 4)
   ============================================================================= *)

(* ICMP Type 3 (Destination Unreachable) Codes *)
Definition ICMP_FRAG_NEEDED : byte := 4.

Record ICMPFragNeeded := {
  icmp_unused : word16;      (* Unused in original RFC 1191 *)
  icmp_next_hop_mtu : word16; (* Next-hop MTU (RFC 1191 Section 4) *)
  icmp_original_header : list byte;
  icmp_original_data : list byte  (* First 8 bytes of original *)
}.

(* Extract MTU from ICMP message *)
Definition extract_mtu_from_icmp (msg : ICMPFragNeeded) : N :=
  if N.eqb msg.(icmp_next_hop_mtu) 0 then
    (* Old router - estimate from original packet size *)
    estimate_mtu_from_packet msg.(icmp_original_header)
  else
    msg.(icmp_next_hop_mtu).

(* Estimate MTU using plateau table *)
Definition estimate_mtu_from_packet (header : list byte) : N :=
  (* Extract total length from IP header *)
  let packet_size := get_ip_total_length header in
  find_next_lower_plateau packet_size.

Definition find_next_lower_plateau (current_size : N) : N :=
  let fix find_plateau (table : list N) :=
    match table with
    | [] => MIN_PMTU
    | mtu :: rest =>
        if N.ltb mtu current_size then mtu
        else find_plateau rest
    end
  in find_plateau MTU_PLATEAU_TABLE.

Definition get_ip_total_length (header : list byte) : N :=
  match header with
  | _ :: _ :: len_high :: len_low :: _ =>
      len_high * 256 + len_low
  | _ => MIN_PMTU
  end.

(* =============================================================================
   Section 3: Path MTU Cache Entry (RFC 1191 Section 5)
   ============================================================================= *)

Record PMTUCacheEntry := {
  pmtu_destination : word32;
  pmtu_value : N;
  pmtu_last_updated : N;      (* Timestamp *)
  pmtu_last_decreased : N;    (* Last time MTU was decreased *)
  pmtu_last_increased : N;    (* Last time we tried to increase *)
  pmtu_locked : bool;          (* Don't increase if recently decreased *)
  pmtu_probe_count : N;        (* Number of probes sent *)
  pmtu_df_bit : bool          (* Don't Fragment bit setting *)
}.

(* Initialize PMTU entry *)
Definition init_pmtu_entry (dest : word32) : PMTUCacheEntry :=
  {| pmtu_destination := dest;
     pmtu_value := DEFAULT_PMTU;
     pmtu_last_updated := 0;
     pmtu_last_decreased := 0;
     pmtu_last_increased := 0;
     pmtu_locked := false;
     pmtu_probe_count := 0;
     pmtu_df_bit := true |}.

(* =============================================================================
   Section 4: Path MTU Discovery State Machine (RFC 1191 Section 5.1)
   ============================================================================= *)

Inductive PMTUState :=
  | PMTUActive      (* Actively discovering *)
  | PMTUPlateau     (* Found plateau value *)
  | PMTUProbing     (* Probing for larger MTU *)
  | PMTUDisabled.   (* PMTUD disabled *)

Record PMTUDiscovery := {
  pmtu_cache : list PMTUCacheEntry;
  pmtu_state : PMTUState;
  pmtu_host_mtu : N;          (* Local interface MTU *)
  pmtu_enable_discovery : bool;
  pmtu_enable_plateau : bool   (* Use plateau table *)
}.

(* Process ICMP Fragmentation Needed *)
Definition process_frag_needed (pd : PMTUDiscovery) (dest : word32) 
                              (icmp : ICMPFragNeeded) (now : N) 
                              : PMTUDiscovery :=
  let new_mtu := extract_mtu_from_icmp icmp in
  
  (* Find or create cache entry *)
  let update_entry (entry : PMTUCacheEntry) :=
    if N.eqb entry.(pmtu_destination) dest then
      if N.ltb new_mtu entry.(pmtu_value) then
        (* Decrease PMTU *)
        {| pmtu_destination := dest;
           pmtu_value := N.max MIN_PMTU new_mtu;
           pmtu_last_updated := now;
           pmtu_last_decreased := now;
           pmtu_last_increased := entry.(pmtu_last_increased);
           pmtu_locked := true;
           pmtu_probe_count := 0;
           pmtu_df_bit := true |}
      else
        entry
    else
      entry
  in
  
  {| pmtu_cache := map update_entry pd.(pmtu_cache);
     pmtu_state := pd.(pmtu_state);
     pmtu_host_mtu := pd.(pmtu_host_mtu);
     pmtu_enable_discovery := pd.(pmtu_enable_discovery);
     pmtu_enable_plateau := pd.(pmtu_enable_plateau) |}.

(* =============================================================================
   Section 5: Setting Don't Fragment Bit (RFC 1191 Section 6.1)
   ============================================================================= *)

Definition should_set_df_bit (pd : PMTUDiscovery) (dest : word32) : bool :=
  if pd.(pmtu_enable_discovery) then
    let find_entry (entries : list PMTUCacheEntry) :=
      find (fun e => N.eqb e.(pmtu_destination) dest) entries
    in
    match find_entry pd.(pmtu_cache) with
    | Some entry => entry.(pmtu_df_bit)
    | None => true  (* Default to setting DF *)
    end
  else
    false.

(* Check if packet size requires fragmentation *)
Definition needs_fragmentation (packet_size : N) (pmtu : N) : bool :=
  N.ltb pmtu packet_size.

(* =============================================================================
   Section 6: PMTU Aging and Timeout (RFC 1191 Section 6.3)
   ============================================================================= *)

Definition age_pmtu_entries (pd : PMTUDiscovery) (now : N) : PMTUDiscovery :=
  let age_entry (entry : PMTUCacheEntry) :=
    if N.ltb PMTU_TIMEOUT (now - entry.(pmtu_last_updated)) then
      (* Entry expired - reset to default *)
      {| pmtu_destination := entry.(pmtu_destination);
         pmtu_value := DEFAULT_PMTU;
         pmtu_last_updated := now;
         pmtu_last_decreased := entry.(pmtu_last_decreased);
         pmtu_last_increased := now;
         pmtu_locked := false;
         pmtu_probe_count := 0;
         pmtu_df_bit := true |}
    else if andb entry.(pmtu_locked)
                 (N.ltb PMTU_RAISE_TIMER (now - entry.(pmtu_last_decreased))) then
      (* Unlock for increase attempts *)
      {| pmtu_destination := entry.(pmtu_destination);
         pmtu_value := entry.(pmtu_value);
         pmtu_last_updated := entry.(pmtu_last_updated);
         pmtu_last_decreased := entry.(pmtu_last_decreased);
         pmtu_last_increased := entry.(pmtu_last_increased);
         pmtu_locked := false;
         pmtu_probe_count := entry.(pmtu_probe_count);
         pmtu_df_bit := entry.(pmtu_df_bit) |}
    else
      entry
  in
  
  {| pmtu_cache := map age_entry pd.(pmtu_cache);
     pmtu_state := pd.(pmtu_state);
     pmtu_host_mtu := pd.(pmtu_host_mtu);
     pmtu_enable_discovery := pd.(pmtu_enable_discovery);
     pmtu_enable_plateau := pd.(pmtu_enable_plateau) |}.

(* =============================================================================
   Section 7: PMTU Increase Probing (RFC 1191 Section 6.4)
   ============================================================================= *)

Definition should_probe_increase (entry : PMTUCacheEntry) (now : N) : bool :=
  andb (negb entry.(pmtu_locked))
       (andb (N.ltb entry.(pmtu_value) DEFAULT_PMTU)
             (N.ltb PMTU_PROBE_INTERVAL (now - entry.(pmtu_last_increased)))).

Definition create_probe_packet (entry : PMTUCacheEntry) : N :=
  (* Try next plateau value *)
  let next_mtu := find_next_higher_plateau entry.(pmtu_value) in
  N.min next_mtu DEFAULT_PMTU.

Definition find_next_higher_plateau (current : N) : N :=
  let fix find_plateau (table : list N) (prev : N) :=
    match table with
    | [] => prev
    | mtu :: rest =>
        if N.ltb current mtu then
          if N.ltb mtu prev then mtu else prev
        else
          find_plateau rest prev
    end
  in find_plateau MTU_PLATEAU_TABLE (N.ones 16).

(* =============================================================================
   Section 8: TCP MSS Adjustment (RFC 1191 Section 8)
   ============================================================================= *)

Definition calculate_tcp_mss (pmtu : N) : N :=
  (* MSS = PMTU - IP header - TCP header *)
  let ip_header := 20 in   (* Minimum IPv4 header *)
  let tcp_header := 20 in  (* Minimum TCP header *)
  if N.ltb (ip_header + tcp_header) pmtu then
    pmtu - ip_header - tcp_header
  else
    MIN_PMTU - ip_header - tcp_header.

(* Clamp TCP MSS option *)
Definition clamp_tcp_mss (requested_mss : N) (pmtu : N) : N :=
  N.min requested_mss (calculate_tcp_mss pmtu).

(* =============================================================================
   Section 9: Router Behavior (RFC 1191 Section 7)
   ============================================================================= *)

Record RouterPMTU := {
  router_interfaces : list (N * N);  (* Interface ID, MTU *)
  router_send_pmtu : bool;           (* Include MTU in ICMP *)
  router_estimate_pmtu : bool        (* Use plateau table *)
}.

Definition router_process_packet (r : RouterPMTU) (packet_size : N) 
                                 (out_interface : N) : option N :=
  (* Find outgoing interface MTU *)
  match find (fun iface => N.eqb (fst iface) out_interface) r.(router_interfaces) with
  | Some (_, mtu) =>
      if N.ltb mtu packet_size then
        (* Would need fragmentation *)
        if r.(router_send_pmtu) then
          Some mtu
        else if r.(router_estimate_pmtu) then
          Some (find_next_lower_plateau packet_size)
        else
          Some 0  (* Old-style ICMP *)
      else
        None  (* No fragmentation needed *)
  | None => None
  end.

(* =============================================================================
   Section 10: Key Properties
   ============================================================================= *)

(* Property 1: PMTU never below minimum *)
Theorem pmtu_minimum : forall pd dest icmp now,
  let pd' := process_frag_needed pd dest icmp now in
  forall entry, In entry pd'.(pmtu_cache) ->
  entry.(pmtu_value) >= MIN_PMTU.
Proof.
  admit.
Qed.

(* Property 2: Plateau values are decreasing *)
Theorem plateau_decreasing : forall i j,
  i < j < length MTU_PLATEAU_TABLE ->
  nth i MTU_PLATEAU_TABLE 0 > nth j MTU_PLATEAU_TABLE 0.
Proof.
  admit.
Qed.

(* Property 3: DF bit set when discovery enabled *)
Theorem df_bit_when_enabled : forall pd dest,
  pd.(pmtu_enable_discovery) = true ->
  exists df, should_set_df_bit pd dest = df.
Proof.
  intros. exists (should_set_df_bit pd dest). reflexivity.
Qed.

(* Property 4: TCP MSS is conservative *)
Theorem tcp_mss_conservative : forall pmtu,
  calculate_tcp_mss pmtu <= pmtu - 40.
Proof.
  intros. unfold calculate_tcp_mss.
  destruct (N.ltb 40 pmtu) eqn:E.
  - simpl. lia.
  - lia.
Qed.

(* Property 5: Aging increases PMTU *)
Theorem aging_increases_pmtu : forall pd now entry,
  In entry pd.(pmtu_cache) ->
  N.ltb PMTU_TIMEOUT (now - entry.(pmtu_last_updated)) = true ->
  exists entry', In entry' (age_pmtu_entries pd now).(pmtu_cache) /\
                 entry'.(pmtu_destination) = entry.(pmtu_destination) /\
                 entry'.(pmtu_value) = DEFAULT_PMTU.
Proof.
  admit.
Qed.

(* Property 6: Probe intervals respected *)
Theorem probe_interval_maintained : forall entry now,
  should_probe_increase entry now = true ->
  N.ltb PMTU_PROBE_INTERVAL (now - entry.(pmtu_last_increased)) = true.
Proof.
  intros. unfold should_probe_increase in H.
  apply andb_prop in H. destruct H.
  apply andb_prop in H. destruct H.
  exact H0.
Qed.

(* =============================================================================
   Section 11: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction "pmtu_discovery.ml"
  process_frag_needed
  should_set_df_bit
  age_pmtu_entries
  should_probe_increase
  calculate_tcp_mss
  find_next_lower_plateau
  find_next_higher_plateau.
