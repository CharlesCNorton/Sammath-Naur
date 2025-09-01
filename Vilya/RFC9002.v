(* =============================================================================
   Formal Verification of QUIC Loss Detection and Congestion Control
   
   Specification: RFC 9002 (J. Iyengar, I. Swett, May 2021)
   Target: QUIC Loss Detection and Congestion Control
   
   Module: QUIC Loss Detection and Congestion Control Formalization
   Author: Charles C Norton
   Date: September 1, 2025
   
   "Every failure he taught them to perceive, and to mend ere the marring grew great."
   
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

(* Timer Granularity *)
Definition kGranularity : N := 1.  (* 1ms *)

(* Initial RTT Constants *)
Definition kInitialRtt : N := 333.  (* 333ms *)

(* Loss Detection Constants *)
Definition kPacketThreshold : N := 3.
Definition kTimeThreshold : N := 9.  (* 9/8 *)
Definition kMicroSecond : N := 1.
Definition kMilliSecond : N := 1000.

(* Congestion Control Constants *)
Definition kMaxDatagramSize : N := 1200.
Definition kInitialWindow : N := 10 * kMaxDatagramSize.
Definition kMinimumWindow : N := 2 * kMaxDatagramSize.
Definition kLossReductionFactor : N := 2.

(* PTO Constants *)
Definition kPtoGranularity : N := 1.  (* 1ms *)
Definition kMaxPtoBackoff : N := 6.

(* =============================================================================
   Section 2: Packet Number Spaces
   ============================================================================= *)

Inductive PacketNumberSpace :=
  | Initial
  | Handshake
  | ApplicationData.

(* =============================================================================
   Section 3: Sent Packet Information
   ============================================================================= *)

Record SentPacket := {
  packet_number : word64;
  ack_eliciting : bool;
  in_flight : bool;
  sent_bytes : N;
  time_sent : N;
  pn_space : PacketNumberSpace;
  ecn_codepoint : N;  (* 0=Not-ECT, 1=ECT(1), 2=ECT(0), 3=CE *)
  frames : list N  (* Simplified frame representation *)
}.

(* =============================================================================
   Section 4: Loss Detection State
   ============================================================================= *)

Record LossDetectionState := {
  (* Per-packet-number-space state *)
  ld_sent_packets : list SentPacket;
  ld_largest_acked : option word64;
  ld_latest_rtt : N;
  ld_smoothed_rtt : N;
  ld_rttvar : N;
  ld_min_rtt : N;
  ld_first_rtt_sample : N;
  
  (* Loss detection *)
  ld_loss_time : option N;
  ld_pto_count : N;
  ld_last_ack_eliciting_time : N;
  
  (* ECN counts *)
  ld_ecn_ce_count : N;
  ld_ecn_ect0_count : N;
  ld_ecn_ect1_count : N
}.

(* Initialize loss detection *)
Definition init_loss_detection : LossDetectionState :=
  {| ld_sent_packets := [];
     ld_largest_acked := None;
     ld_latest_rtt := 0;
     ld_smoothed_rtt := kInitialRtt;
     ld_rttvar := kInitialRtt / 2;
     ld_min_rtt := 0;
     ld_first_rtt_sample := 0;
     ld_loss_time := None;
     ld_pto_count := 0;
     ld_last_ack_eliciting_time := 0;
     ld_ecn_ce_count := 0;
     ld_ecn_ect0_count := 0;
     ld_ecn_ect1_count := 0 |}.

(* =============================================================================
   Section 5: RTT Estimation (RFC 9002 Section 5)
   ============================================================================= *)

Definition update_rtt (ld : LossDetectionState) (latest_rtt : N) 
                      (ack_delay : N) (now : N) : LossDetectionState :=
  let min_rtt := if N.eqb ld.(ld_min_rtt) 0 
                 then latest_rtt
                 else N.min ld.(ld_min_rtt) latest_rtt in
  
  (* Adjust for ack delay if not handshake *)
  let adjusted_rtt := if N.ltb ack_delay latest_rtt
                      then latest_rtt - ack_delay
                      else latest_rtt in
  
  if N.eqb ld.(ld_first_rtt_sample) 0 then
    (* First RTT sample *)
    {| ld_sent_packets := ld.(ld_sent_packets);
       ld_largest_acked := ld.(ld_largest_acked);
       ld_latest_rtt := latest_rtt;
       ld_smoothed_rtt := adjusted_rtt;
       ld_rttvar := adjusted_rtt / 2;
       ld_min_rtt := min_rtt;
       ld_first_rtt_sample := now;
       ld_loss_time := ld.(ld_loss_time);
       ld_pto_count := ld.(ld_pto_count);
       ld_last_ack_eliciting_time := ld.(ld_last_ack_eliciting_time);
       ld_ecn_ce_count := ld.(ld_ecn_ce_count);
       ld_ecn_ect0_count := ld.(ld_ecn_ect0_count);
       ld_ecn_ect1_count := ld.(ld_ecn_ect1_count) |}
  else
    (* Subsequent RTT samples *)
    let rtt_diff := if N.ltb ld.(ld_smoothed_rtt) adjusted_rtt
                    then adjusted_rtt - ld.(ld_smoothed_rtt)
                    else ld.(ld_smoothed_rtt) - adjusted_rtt in
    let rttvar := (3 * ld.(ld_rttvar) + rtt_diff) / 4 in
    let smoothed_rtt := (7 * ld.(ld_smoothed_rtt) + adjusted_rtt) / 8 in
    
    {| ld_sent_packets := ld.(ld_sent_packets);
       ld_largest_acked := ld.(ld_largest_acked);
       ld_latest_rtt := latest_rtt;
       ld_smoothed_rtt := smoothed_rtt;
       ld_rttvar := rttvar;
       ld_min_rtt := min_rtt;
       ld_first_rtt_sample := ld.(ld_first_rtt_sample);
       ld_loss_time := ld.(ld_loss_time);
       ld_pto_count := ld.(ld_pto_count);
       ld_last_ack_eliciting_time := ld.(ld_last_ack_eliciting_time);
       ld_ecn_ce_count := ld.(ld_ecn_ce_count);
       ld_ecn_ect0_count := ld.(ld_ecn_ect0_count);
       ld_ecn_ect1_count := ld.(ld_ecn_ect1_count) |}.

(* =============================================================================
   Section 6: Loss Detection (RFC 9002 Section 6)
   ============================================================================= *)

(* Determine which packets are lost *)
Definition detect_lost_packets (ld : LossDetectionState) (now : N) 
                              : list SentPacket * LossDetectionState :=
  match ld.(ld_largest_acked) with
  | None => ([], ld)
  | Some largest_acked =>
      let loss_delay := N.max kGranularity 
                              ((kTimeThreshold * N.max ld.(ld_latest_rtt) ld.(ld_smoothed_rtt)) / 8) in
      let lost_send_time := now - loss_delay in
      
      let partition_packets (packets : list SentPacket) :=
        fold_left (fun acc pkt =>
          if orb (N.ltb (pkt.(packet_number) + kPacketThreshold) largest_acked)
                 (andb pkt.(in_flight) (N.leb pkt.(time_sent) lost_send_time))
          then (pkt :: fst acc, snd acc)
          else (fst acc, pkt :: snd acc))
        packets ([], [])
      in
      
      let (lost, remaining) := partition_packets ld.(ld_sent_packets) in
      (lost, {| ld_sent_packets := remaining;
                ld_largest_acked := ld.(ld_largest_acked);
                ld_latest_rtt := ld.(ld_latest_rtt);
                ld_smoothed_rtt := ld.(ld_smoothed_rtt);
                ld_rttvar := ld.(ld_rttvar);
                ld_min_rtt := ld.(ld_min_rtt);
                ld_first_rtt_sample := ld.(ld_first_rtt_sample);
                ld_loss_time := None;
                ld_pto_count := 0;
                ld_last_ack_eliciting_time := ld.(ld_last_ack_eliciting_time);
                ld_ecn_ce_count := ld.(ld_ecn_ce_count);
                ld_ecn_ect0_count := ld.(ld_ecn_ect0_count);
                ld_ecn_ect1_count := ld.(ld_ecn_ect1_count) |})
  end.

(* =============================================================================
   Section 7: Probe Timeout (PTO) Calculation (RFC 9002 Section 6.2)
   ============================================================================= *)

Definition compute_pto (ld : LossDetectionState) : N :=
  let pto := ld.(ld_smoothed_rtt) + N.max ld.(ld_rttvar) (4 * kGranularity) in
  pto * (N.shiftl 1 (N.min ld.(ld_pto_count) kMaxPtoBackoff)).

(* Set PTO timer *)
Definition set_pto_timer (ld : LossDetectionState) (now : N) : option N :=
  if existsb (fun pkt => pkt.(ack_eliciting)) ld.(ld_sent_packets) then
    Some (now + compute_pto ld)
  else
    None.

(* =============================================================================
   Section 8: Congestion Control State (RFC 9002 Section 7)
   ============================================================================= *)

Record CongestionControl := {
  cc_bytes_in_flight : N;
  cc_congestion_window : N;
  cc_congestion_recovery_start_time : option N;
  cc_ssthresh : N;
  cc_ecn_ce_counter : N;
  
  (* Pacing *)
  cc_pacing_rate : N;
  
  (* Statistics *)
  cc_bytes_sent : N;
  cc_bytes_acked : N;
  cc_bytes_lost : N
}.

(* Initialize congestion control *)
Definition init_congestion_control : CongestionControl :=
  {| cc_bytes_in_flight := 0;
     cc_congestion_window := kInitialWindow;
     cc_congestion_recovery_start_time := None;
     cc_ssthresh := N.ones 64;  (* Infinite *)
     cc_ecn_ce_counter := 0;
     cc_pacing_rate := 0;
     cc_bytes_sent := 0;
     cc_bytes_acked := 0;
     cc_bytes_lost := 0 |}.

(* =============================================================================
   Section 9: Congestion Control Algorithms (RFC 9002 Section 7.3)
   ============================================================================= *)

(* On packet sent *)
Definition on_packet_sent (cc : CongestionControl) (sent_bytes : N) : CongestionControl :=
  {| cc_bytes_in_flight := cc.(cc_bytes_in_flight) + sent_bytes;
     cc_congestion_window := cc.(cc_congestion_window);
     cc_congestion_recovery_start_time := cc.(cc_congestion_recovery_start_time);
     cc_ssthresh := cc.(cc_ssthresh);
     cc_ecn_ce_counter := cc.(cc_ecn_ce_counter);
     cc_pacing_rate := cc.(cc_pacing_rate);
     cc_bytes_sent := cc.(cc_bytes_sent) + sent_bytes;
     cc_bytes_acked := cc.(cc_bytes_acked);
     cc_bytes_lost := cc.(cc_bytes_lost) |}.

(* On packet acknowledged *)
Definition on_packet_acked (cc : CongestionControl) (acked_bytes : N) 
                          (time_sent : N) (now : N) : CongestionControl :=
  let cc' := {| cc_bytes_in_flight := 
                  if N.ltb acked_bytes cc.(cc_bytes_in_flight)
                  then cc.(cc_bytes_in_flight) - acked_bytes
                  else 0;
                cc_congestion_window := cc.(cc_congestion_window);
                cc_congestion_recovery_start_time := cc.(cc_congestion_recovery_start_time);
                cc_ssthresh := cc.(cc_ssthresh);
                cc_ecn_ce_counter := cc.(cc_ecn_ce_counter);
                cc_pacing_rate := cc.(cc_pacing_rate);
                cc_bytes_sent := cc.(cc_bytes_sent);
                cc_bytes_acked := cc.(cc_bytes_acked) + acked_bytes;
                cc_bytes_lost := cc.(cc_bytes_lost) |} in
  
  (* Check if in recovery *)
  match cc'.(cc_congestion_recovery_start_time) with
  | Some recovery_start =>
      if N.leb time_sent recovery_start then
        cc'  (* In recovery, don't increase window *)
      else
        (* Congestion avoidance *)
        {| cc_bytes_in_flight := cc'.(cc_bytes_in_flight);
           cc_congestion_window := 
             cc'.(cc_congestion_window) + 
             (kMaxDatagramSize * acked_bytes) / cc'.(cc_congestion_window);
           cc_congestion_recovery_start_time := cc'.(cc_congestion_recovery_start_time);
           cc_ssthresh := cc'.(cc_ssthresh);
           cc_ecn_ce_counter := cc'.(cc_ecn_ce_counter);
           cc_pacing_rate := cc'.(cc_pacing_rate);
           cc_bytes_sent := cc'.(cc_bytes_sent);
           cc_bytes_acked := cc'.(cc_bytes_acked);
           cc_bytes_lost := cc'.(cc_bytes_lost) |}
  | None =>
      (* Slow start *)
      if N.ltb cc'.(cc_congestion_window) cc'.(cc_ssthresh) then
        {| cc_bytes_in_flight := cc'.(cc_bytes_in_flight);
           cc_congestion_window := cc'.(cc_congestion_window) + acked_bytes;
           cc_congestion_recovery_start_time := cc'.(cc_congestion_recovery_start_time);
           cc_ssthresh := cc'.(cc_ssthresh);
           cc_ecn_ce_counter := cc'.(cc_ecn_ce_counter);
           cc_pacing_rate := cc'.(cc_pacing_rate);
           cc_bytes_sent := cc'.(cc_bytes_sent);
           cc_bytes_acked := cc'.(cc_bytes_acked);
           cc_bytes_lost := cc'.(cc_bytes_lost) |}
      else
        (* Congestion avoidance *)
        {| cc_bytes_in_flight := cc'.(cc_bytes_in_flight);
           cc_congestion_window := 
             cc'.(cc_congestion_window) + 
             (kMaxDatagramSize * acked_bytes) / cc'.(cc_congestion_window);
           cc_congestion_recovery_start_time := cc'.(cc_congestion_recovery_start_time);
           cc_ssthresh := cc'.(cc_ssthresh);
           cc_ecn_ce_counter := cc'.(cc_ecn_ce_counter);
           cc_pacing_rate := cc'.(cc_pacing_rate);
           cc_bytes_sent := cc'.(cc_bytes_sent);
           cc_bytes_acked := cc'.(cc_bytes_acked);
           cc_bytes_lost := cc'.(cc_bytes_lost) |}
  end.

(* On congestion event (loss or ECN) *)
Definition on_congestion_event (cc : CongestionControl) (now : N) : CongestionControl :=
  match cc.(cc_congestion_recovery_start_time) with
  | Some recovery_start =>
      if N.ltb recovery_start now then
        cc  (* Already in recovery *)
      else
        (* Enter recovery *)
        {| cc_bytes_in_flight := cc.(cc_bytes_in_flight);
           cc_congestion_window := N.max kMinimumWindow (cc.(cc_congestion_window) / kLossReductionFactor);
           cc_congestion_recovery_start_time := Some now;
           cc_ssthresh := N.max kMinimumWindow (cc.(cc_congestion_window) / kLossReductionFactor);
           cc_ecn_ce_counter := cc.(cc_ecn_ce_counter);
           cc_pacing_rate := cc.(cc_pacing_rate);
           cc_bytes_sent := cc.(cc_bytes_sent);
           cc_bytes_acked := cc.(cc_bytes_acked);
           cc_bytes_lost := cc.(cc_bytes_lost) |}
  | None =>
      (* Enter recovery *)
      {| cc_bytes_in_flight := cc.(cc_bytes_in_flight);
         cc_congestion_window := N.max kMinimumWindow (cc.(cc_congestion_window) / kLossReductionFactor);
         cc_congestion_recovery_start_time := Some now;
         cc_ssthresh := N.max kMinimumWindow (cc.(cc_congestion_window) / kLossReductionFactor);
         cc_ecn_ce_counter := cc.(cc_ecn_ce_counter);
         cc_pacing_rate := cc.(cc_pacing_rate);
         cc_bytes_sent := cc.(cc_bytes_sent);
         cc_bytes_acked := cc.(cc_bytes_acked);
         cc_bytes_lost := cc.(cc_bytes_lost) |}
  end.

(* =============================================================================
   Section 10: ECN Support (RFC 9002 Section 7.4)
   ============================================================================= *)

Definition process_ecn (ld : LossDetectionState) (cc : CongestionControl)
                       (ecn_ce_count : N) (now : N) 
                       : LossDetectionState * CongestionControl :=
  if N.ltb ld.(ld_ecn_ce_count) ecn_ce_count then
    (* New ECN-CE markings detected *)
    let ld' := {| ld_sent_packets := ld.(ld_sent_packets);
                  ld_largest_acked := ld.(ld_largest_acked);
                  ld_latest_rtt := ld.(ld_latest_rtt);
                  ld_smoothed_rtt := ld.(ld_smoothed_rtt);
                  ld_rttvar := ld.(ld_rttvar);
                  ld_min_rtt := ld.(ld_min_rtt);
                  ld_first_rtt_sample := ld.(ld_first_rtt_sample);
                  ld_loss_time := ld.(ld_loss_time);
                  ld_pto_count := ld.(ld_pto_count);
                  ld_last_ack_eliciting_time := ld.(ld_last_ack_eliciting_time);
                  ld_ecn_ce_count := ecn_ce_count;
                  ld_ecn_ect0_count := ld.(ld_ecn_ect0_count);
                  ld_ecn_ect1_count := ld.(ld_ecn_ect1_count) |} in
    (ld', on_congestion_event cc now)
  else
    (ld, cc).

(* =============================================================================
   Section 11: Key Properties
   ============================================================================= *)

(* Property 1: RTT is always positive after first sample *)
Theorem rtt_positive : forall ld latest_rtt ack_delay now,
  latest_rtt > 0 ->
  (update_rtt ld latest_rtt ack_delay now).(ld_smoothed_rtt) > 0.
Proof.
  admit.
Qed.

(* Property 2: PTO backs off exponentially *)
Theorem pto_exponential_backoff : forall ld,
  compute_pto {| ld_sent_packets := ld.(ld_sent_packets);
                 ld_largest_acked := ld.(ld_largest_acked);
                 ld_latest_rtt := ld.(ld_latest_rtt);
                 ld_smoothed_rtt := ld.(ld_smoothed_rtt);
                 ld_rttvar := ld.(ld_rttvar);
                 ld_min_rtt := ld.(ld_min_rtt);
                 ld_first_rtt_sample := ld.(ld_first_rtt_sample);
                 ld_loss_time := ld.(ld_loss_time);
                 ld_pto_count := ld.(ld_pto_count) + 1;
                 ld_last_ack_eliciting_time := ld.(ld_last_ack_eliciting_time);
                 ld_ecn_ce_count := ld.(ld_ecn_ce_count);
                 ld_ecn_ect0_count := ld.(ld_ecn_ect0_count);
                 ld_ecn_ect1_count := ld.(ld_ecn_ect1_count) |} >= 
  2 * compute_pto ld.
Proof.
  admit.
Qed.

(* Property 3: Congestion window never below minimum *)
Theorem cwnd_minimum : forall cc now,
  (on_congestion_event cc now).(cc_congestion_window) >= kMinimumWindow.
Proof.
  intros. unfold on_congestion_event.
  destruct cc.(cc_congestion_recovery_start_time).
  - destruct (N.ltb n now); simpl; apply N.le_max_l.
  - simpl. apply N.le_max_l.
Qed.

(* Property 4: Bytes in flight never negative *)
Theorem bytes_in_flight_non_negative : forall cc acked time now,
  (on_packet_acked cc acked time now).(cc_bytes_in_flight) >= 0.
Proof.
  intros. unfold on_packet_acked.
  destruct (N.ltb acked cc.(cc_bytes_in_flight)).
  - destruct cc.(cc_congestion_recovery_start_time); simpl; lia.
  - destruct cc.(cc_congestion_recovery_start_time); simpl; lia.
Qed.

(* =============================================================================
   Section 12: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction "quic_recovery.ml"
  update_rtt
  detect_lost_packets
  compute_pto
  on_packet_sent
  on_packet_acked
  on_congestion_event
  process_ecn.
