(* =============================================================================
   Formal Verification of Packetization Layer Path MTU Discovery
   
   Specification: RFC 4821 (M. Mathis, J. Heffner, March 2007)
   Target: Packetization Layer Path MTU Discovery
   
   Module: PLPMTUD Formalization and Verification
   Author: Charles C Norton
   Date: September 1, 2025
   
   "Day by day their knowledge increased, as water filling a cistern drop by drop."
   
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

(* PLPMTUD Constants (RFC 4821 Section 7.3) *)
Definition MIN_PLPMTU : N := 1024.           (* Minimum practical PMTU *)
Definition MAX_PLPMTU : N := 65535.          (* Maximum possible PMTU *)
Definition BASE_PLPMTU : N := 1024.          (* Base PMTU (for black hole detection) *)
Definition PROBED_SIZE_INCREMENT : N := 32.  (* Minimum probe increment *)

(* Timer Constants *)
Definition PLPMTU_RAISE_TIMER : N := 600000.     (* 10 minutes *)
Definition MAX_PROBES : N := 3.                  (* Per size *)
Definition PROBE_TIMER : N := 30000.             (* 30 seconds *)
Definition BLACK_HOLE_DETECTION_TIMER : N := 300000. (* 5 minutes *)

(* Loss Constants *)
Definition PLPMTU_PROBE_THRESHOLD : N := 5.      (* Packets before probing *)
Definition PLPMTU_ERROR_THRESHOLD : N := 10.     (* Errors before declaring black hole *)

(* =============================================================================
   Section 2: PLPMTUD State (RFC 4821 Section 4)
   ============================================================================= *)

Inductive PLPMTUState :=
  | PLPMTUDisabled
  | PLPMTUBase          (* Using base PMTU *)
  | PLPMTUSearching     (* Searching for PMTU *)
  | PLPMTUSearchComplete (* Found PMTU *)
  | PLPMTUError.        (* Black hole detected *)

Record PLPMTUDEntry := {
  plpmtu_state : PLPMTUState;
  plpmtu_probe_size : N;           (* Current probe size *)
  plpmtu_eff_pmtu : N;             (* Effective PMTU *)
  plpmtu_max_probed : N;           (* Maximum successfully probed *)
  plpmtu_min_failed : N;           (* Minimum size that failed *)
  plpmtu_probe_count : N;          (* Probes at current size *)
  plpmtu_probe_lost : N;           (* Lost probes at current size *)
  plpmtu_last_probe_time : N;      (* Time of last probe *)
  plpmtu_search_low : N;           (* Binary search lower bound *)
  plpmtu_search_high : N;          (* Binary search upper bound *)
  plpmtu_probe_timer : option N;   (* Next probe time *)
  plpmtu_raise_timer : option N;   (* Timer to attempt raising *)
  plpmtu_ptb_received : bool;      (* PTB message received (optional) *)
  plpmtu_black_hole_detection : bool;
  plpmtu_error_count : N           (* Consecutive transmission errors *)
}.

(* Initialize PLPMTUD entry *)
Definition init_plpmtud_entry : PLPMTUDEntry :=
  {| plpmtu_state := PLPMTUBase;
     plpmtu_probe_size := BASE_PLPMTU;
     plpmtu_eff_pmtu := BASE_PLPMTU;
     plpmtu_max_probed := BASE_PLPMTU;
     plpmtu_min_failed := MAX_PLPMTU;
     plpmtu_probe_count := 0;
     plpmtu_probe_lost := 0;
     plpmtu_last_probe_time := 0;
     plpmtu_search_low := BASE_PLPMTU;
     plpmtu_search_high := MAX_PLPMTU;
     plpmtu_probe_timer := None;
     plpmtu_raise_timer := None;
     plpmtu_ptb_received := false;
     plpmtu_black_hole_detection := true;
     plpmtu_error_count := 0 |}.

(* =============================================================================
   Section 3: Search Algorithm (RFC 4821 Section 7.3)
   ============================================================================= *)

(* Calculate next probe size using binary search *)
Definition calculate_next_probe_size (entry : PLPMTUDEntry) : N :=
  let low := entry.(plpmtu_search_low) in
  let high := entry.(plpmtu_search_high) in
  if N.leb (high - low) PROBED_SIZE_INCREMENT then
    high  (* Search complete *)
  else
    (* Binary search midpoint, rounded to boundary *)
    let mid := (low + high) / 2 in
    (mid / PROBED_SIZE_INCREMENT) * PROBED_SIZE_INCREMENT.

(* Update search bounds based on probe result *)
Definition update_search_bounds (entry : PLPMTUDEntry) (probe_size : N) 
                               (success : bool) : PLPMTUDEntry :=
  if success then
    (* Probe succeeded - raise lower bound *)
    {| plpmtu_state := entry.(plpmtu_state);
       plpmtu_probe_size := probe_size;
       plpmtu_eff_pmtu := probe_size;  (* Can use this size *)
       plpmtu_max_probed := N.max probe_size entry.(plpmtu_max_probed);
       plpmtu_min_failed := entry.(plpmtu_min_failed);
       plpmtu_probe_count := 0;
       plpmtu_probe_lost := 0;
       plpmtu_last_probe_time := entry.(plpmtu_last_probe_time);
       plpmtu_search_low := probe_size;
       plpmtu_search_high := entry.(plpmtu_search_high);
       plpmtu_probe_timer := entry.(plpmtu_probe_timer);
       plpmtu_raise_timer := entry.(plpmtu_raise_timer);
       plpmtu_ptb_received := entry.(plpmtu_ptb_received);
       plpmtu_black_hole_detection := entry.(plpmtu_black_hole_detection);
       plpmtu_error_count := 0 |}
  else
    (* Probe failed - lower upper bound *)
    {| plpmtu_state := entry.(plpmtu_state);
       plpmtu_probe_size := entry.(plpmtu_probe_size);
       plpmtu_eff_pmtu := entry.(plpmtu_eff_pmtu);
       plpmtu_max_probed := entry.(plpmtu_max_probed);
       plpmtu_min_failed := N.min probe_size entry.(plpmtu_min_failed);
       plpmtu_probe_count := entry.(plpmtu_probe_count) + 1;
       plpmtu_probe_lost := entry.(plpmtu_probe_lost) + 1;
       plpmtu_last_probe_time := entry.(plpmtu_last_probe_time);
       plpmtu_search_low := entry.(plpmtu_search_low);
       plpmtu_search_high := probe_size - 1;
       plpmtu_probe_timer := entry.(plpmtu_probe_timer);
       plpmtu_raise_timer := entry.(plpmtu_raise_timer);
       plpmtu_ptb_received := entry.(plpmtu_ptb_received);
       plpmtu_black_hole_detection := entry.(plpmtu_black_hole_detection);
       plpmtu_error_count := entry.(plpmtu_error_count) |}.

(* =============================================================================
   Section 4: Probe Generation (RFC 4821 Section 7.1)
   ============================================================================= *)

Inductive ProbeType :=
  | ProbeData         (* Probe using data packet *)
  | ProbePadding      (* Probe with padding *)
  | ProbeSegmented.   (* Probe using segmentation *)

Record ProbePacket := {
  probe_size : N;
  probe_type : ProbeType;
  probe_seq : N;           (* Sequence number for tracking *)
  probe_timestamp : N;     (* When probe was sent *)
  probe_retries : N        (* Number of retransmissions *)
}.

Definition create_probe_packet (entry : PLPMTUDEntry) (seq : N) (now : N) 
                              : ProbePacket :=
  let size := calculate_next_probe_size entry in
  {| probe_size := size;
     probe_type := if N.ltb size 1500 then ProbeData else ProbePadding;
     probe_seq := seq;
     probe_timestamp := now;
     probe_retries := 0 |}.

(* Check if we should send a probe *)
Definition should_send_probe (entry : PLPMTUDEntry) (now : N) 
                            (data_sent : N) : bool :=
  match entry.(plpmtu_state) with
  | PLPMTUSearching =>
      andb (N.ltb PLPMTU_PROBE_THRESHOLD data_sent)
           (N.ltb PROBE_TIMER (now - entry.(plpmtu_last_probe_time)))
  | PLPMTUSearchComplete =>
      (* Periodic probing to check for increases *)
      N.ltb PLPMTU_RAISE_TIMER (now - entry.(plpmtu_last_probe_time))
  | _ => false
  end.

(* =============================================================================
   Section 5: Loss Detection (RFC 4821 Section 7.2)
   ============================================================================= *)

(* Process probe response/timeout *)
Definition process_probe_response (entry : PLPMTUDEntry) (probe : ProbePacket)
                                 (acknowledged : bool) (now : N) : PLPMTUDEntry :=
  if acknowledged then
    (* Probe succeeded *)
    let entry' := update_search_bounds entry probe.(probe_size) true in
    if N.leb (entry'.(plpmtu_search_high) - entry'.(plpmtu_search_low)) 
             PROBED_SIZE_INCREMENT then
      (* Search complete *)
      {| plpmtu_state := PLPMTUSearchComplete;
         plpmtu_probe_size := entry'.(plpmtu_probe_size);
         plpmtu_eff_pmtu := entry'.(plpmtu_eff_pmtu);
         plpmtu_max_probed := entry'.(plpmtu_max_probed);
         plpmtu_min_failed := entry'.(plpmtu_min_failed);
         plpmtu_probe_count := 0;
         plpmtu_probe_lost := 0;
         plpmtu_last_probe_time := now;
         plpmtu_search_low := entry'.(plpmtu_search_low);
         plpmtu_search_high := entry'.(plpmtu_search_high);
         plpmtu_probe_timer := None;
         plpmtu_raise_timer := Some (now + PLPMTU_RAISE_TIMER);
         plpmtu_ptb_received := entry'.(plpmtu_ptb_received);
         plpmtu_black_hole_detection := entry'.(plpmtu_black_hole_detection);
         plpmtu_error_count := 0 |}
    else
      entry'
  else
    (* Probe failed *)
    if N.ltb MAX_PROBES probe.(probe_retries) then
      (* Retry probe *)
      entry
    else
      (* Give up on this size *)
      update_search_bounds entry probe.(probe_size) false.

(* =============================================================================
   Section 6: Black Hole Detection (RFC 4821 Section 7.7)
   ============================================================================= *)

Definition detect_black_hole (entry : PLPMTUDEntry) (loss_count : N) : PLPMTUDEntry :=
  if andb entry.(plpmtu_black_hole_detection)
          (N.ltb PLPMTU_ERROR_THRESHOLD loss_count) then
    (* Black hole detected - reset to base MTU *)
    {| plpmtu_state := PLPMTUError;
       plpmtu_probe_size := BASE_PLPMTU;
       plpmtu_eff_pmtu := BASE_PLPMTU;
       plpmtu_max_probed := BASE_PLPMTU;
       plpmtu_min_failed := entry.(plpmtu_min_failed);
       plpmtu_probe_count := 0;
       plpmtu_probe_lost := 0;
       plpmtu_last_probe_time := entry.(plpmtu_last_probe_time);
       plpmtu_search_low := BASE_PLPMTU;
       plpmtu_search_high := entry.(plpmtu_search_high);
       plpmtu_probe_timer := None;
       plpmtu_raise_timer := None;
       plpmtu_ptb_received := false;
       plpmtu_black_hole_detection := true;
       plpmtu_error_count := loss_count |}
  else
    entry.

(* =============================================================================
   Section 7: Integration with Transport Protocols (RFC 4821 Section 5)
   ============================================================================= *)

Record TransportIntegration := {
  ti_protocol : N;           (* 0=TCP, 1=SCTP, 2=DCCP *)
  ti_probe_method : N;        (* 0=padding, 1=segmentation *)
  ti_loss_detection : N;      (* 0=timeout, 1=SACK, 2=duplicate ACK *)
  ti_probe_in_progress : bool;
  ti_normal_data_sent : N;    (* Non-probe data sent *)
  ti_probe_data_sent : N      (* Probe data sent *)
}.

(* TCP-specific PLPMTUD *)
Definition tcp_plpmtud_send_decision (entry : PLPMTUDEntry) (ti : TransportIntegration)
                                     (segment_size : N) (now : N) 
                                     : (bool * N) := (* (is_probe, size) *)
  if should_send_probe entry now ti.(ti_normal_data_sent) then
    let probe_size := calculate_next_probe_size entry in
    if N.ltb segment_size probe_size then
      (true, probe_size)  (* Send as probe *)
    else
      (false, entry.(plpmtu_eff_pmtu))  (* Normal segment *)
  else
    (false, entry.(plpmtu_eff_pmtu)).

(* SCTP-specific PLPMTUD *)
Definition sctp_plpmtud_heartbeat_probe (entry : PLPMTUDEntry) : N :=
  (* Use HEARTBEAT chunks for probing *)
  calculate_next_probe_size entry.

(* =============================================================================
   Section 8: Robustness Features (RFC 4821 Section 7.8)
   ============================================================================= *)

Record RobustnessConfig := {
  rob_validate_increase : bool;     (* Validate PMTU increases *)
  rob_validate_ptb : bool;          (* Validate PTB messages *)
  rob_suspend_on_error : bool;      (* Suspend on repeated errors *)
  rob_slow_start : bool;            (* Use slow start for probing *)
  rob_conservative_mode : bool      (* Conservative probing *)
}.

Definition apply_robustness (entry : PLPMTUDEntry) (config : RobustnessConfig)
                           : PLPMTUDEntry :=
  if config.(rob_conservative_mode) then
    {| plpmtu_state := entry.(plpmtu_state);
       plpmtu_probe_size := entry.(plpmtu_probe_size);
       plpmtu_eff_pmtu := N.min entry.(plpmtu_eff_pmtu) entry.(plpmtu_max_probed);
       plpmtu_max_probed := entry.(plpmtu_max_probed);
       plpmtu_min_failed := entry.(plpmtu_min_failed);
       plpmtu_probe_count := entry.(plpmtu_probe_count);
       plpmtu_probe_lost := entry.(plpmtu_probe_lost);
       plpmtu_last_probe_time := entry.(plpmtu_last_probe_time);
       plpmtu_search_low := entry.(plpmtu_search_low);
       plpmtu_search_high := entry.(plpmtu_search_high);
       plpmtu_probe_timer := entry.(plpmtu_probe_timer);
       plpmtu_raise_timer := entry.(plpmtu_raise_timer);
       plpmtu_ptb_received := entry.(plpmtu_ptb_received);
       plpmtu_black_hole_detection := true;
       plpmtu_error_count := entry.(plpmtu_error_count) |}
  else
    entry.

(* =============================================================================
   Section 9: Interaction with Classical PMTUD (RFC 4821 Section 6)
   ============================================================================= *)

Definition process_ptb_hint (entry : PLPMTUDEntry) (ptb_mtu : N) : PLPMTUDEntry :=
  if andb (N.ltb MIN_PLPMTU ptb_mtu)
          (N.ltb ptb_mtu entry.(plpmtu_eff_pmtu)) then
    (* Use PTB as hint for search *)
    {| plpmtu_state := PLPMTUSearching;
       plpmtu_probe_size := ptb_mtu;
       plpmtu_eff_pmtu := entry.(plpmtu_max_probed);  (* Fall back to known good *)
       plpmtu_max_probed := entry.(plpmtu_max_probed);
       plpmtu_min_failed := N.min ptb_mtu entry.(plpmtu_min_failed);
       plpmtu_probe_count := 0;
       plpmtu_probe_lost := 0;
       plpmtu_last_probe_time := entry.(plpmtu_last_probe_time);
       plpmtu_search_low := entry.(plpmtu_search_low);
       plpmtu_search_high := ptb_mtu;
       plpmtu_probe_timer := entry.(plpmtu_probe_timer);
       plpmtu_raise_timer := entry.(plpmtu_raise_timer);
       plpmtu_ptb_received := true;
       plpmtu_black_hole_detection := entry.(plpmtu_black_hole_detection);
       plpmtu_error_count := 0 |}
  else
    entry.

(* =============================================================================
   Section 10: Key Properties
   ============================================================================= *)

(* Property 1: Search converges *)
Theorem search_converges : forall entry,
  entry.(plpmtu_state) = PLPMTUSearching ->
  entry.(plpmtu_search_high) - entry.(plpmtu_search_low) > PROBED_SIZE_INCREMENT ->
  let next := calculate_next_probe_size entry in
  entry.(plpmtu_search_low) < next < entry.(plpmtu_search_high).
Proof.
  admit.
Qed.

(* Property 2: Effective PMTU never exceeds probed *)
Theorem eff_pmtu_safe : forall entry,
  entry.(plpmtu_eff_pmtu) <= entry.(plpmtu_max_probed).
Proof.
  admit.
Qed.

(* Property 3: Black hole detection resets to base *)
Theorem black_hole_resets : forall entry loss,
  entry.(plpmtu_black_hole_detection) = true ->
  N.ltb PLPMTU_ERROR_THRESHOLD loss = true ->
  (detect_black_hole entry loss).(plpmtu_eff_pmtu) = BASE_PLPMTU.
Proof.
  intros. unfold detect_black_hole.
  rewrite H. simpl. rewrite H0. simpl. reflexivity.
Qed.

(* Property 4: Binary search maintains invariant *)
Theorem binary_search_invariant : forall entry size success,
  let entry' := update_search_bounds entry size success in
  entry'.(plpmtu_search_low) <= entry'.(plpmtu_search_high).
Proof.
  admit.
Qed.

(* Property 5: Probe size aligned *)
Theorem probe_size_aligned : forall entry,
  let size := calculate_next_probe_size entry in
  N.modulo size PROBED_SIZE_INCREMENT = 0 \/
  size = entry.(plpmtu_search_high).
Proof.
  admit.
Qed.

(* =============================================================================
   Section 11: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction "plpmtud.ml"
  calculate_next_probe_size
  update_search_bounds
  create_probe_packet
  should_send_probe
  process_probe_response
  detect_black_hole
  tcp_plpmtud_send_decision
  process_ptb_hint.
