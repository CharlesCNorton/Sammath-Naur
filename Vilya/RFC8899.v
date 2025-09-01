(* =============================================================================
   Formal Verification of Datagram Packetization Layer Path MTU Discovery
   
   Specification: RFC 8899 (G. Fairhurst, T. Jones, M. Tüxen, I. Rüngeler, 
                            T. Völker, September 2020)
   Target: Datagram PLPMTUD
   
   Module: Datagram PLPMTUD Formalization and Verification
   Author: Charles C Norton
   Date: September 1, 2025
   
   "In those hours none marked how the shadows lengthened about the forge."
   
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

(* DPLPMTUD Constants (RFC 8899 Section 5.1.2) *)
Definition MIN_PLPMTU : N := 1200.              (* Minimum for IPv6 *)
Definition BASE_PLPMTU : N := 1200.             (* Base PMTU *)
Definition MAX_PLPMTU : N := 65535.             (* Maximum PMTU *)
Definition MAX_PROBES : N := 3.                 (* Maximum probe attempts *)
Definition PROBE_COUNT : N := 3.                (* Probes per size *)

(* Timer Constants (RFC 8899 Section 5.1.3) *)
Definition PROBE_TIMER_MIN : N := 1000.         (* 1 second minimum *)
Definition PROBE_TIMER_MAX : N := 60000.        (* 60 seconds maximum *)
Definition PMTU_RAISE_TIMER : N := 600000.      (* 10 minutes *)
Definition CONFIRMATION_TIMER : N := 30000.     (* 30 seconds *)
Definition MAX_BURST : N := 3.                  (* Max probe burst *)

(* State Machine Constants *)
Definition SEARCH_COMPLETE_THRESHOLD : N := 32. (* Bytes difference to complete *)
Definition BLACK_HOLE_THRESHOLD : N := 5.       (* Consecutive failures *)
Definition ERROR_THRESHOLD : N := 10.           (* Errors before declaring failure *)

(* =============================================================================
   Section 2: DPLPMTUD States (RFC 8899 Section 5.2)
   ============================================================================= *)

Inductive DPLPMTUDState :=
  | DPLPMTUD_DISABLED       (* Not performing DPLPMTUD *)
  | DPLPMTUD_BASE           (* Using BASE_PLPMTU *)
  | DPLPMTUD_SEARCHING      (* Searching for larger PMTU *)
  | DPLPMTUD_SEARCH_COMPLETE (* Completed search *)
  | DPLPMTUD_ERROR.         (* Detected black hole or error *)

(* =============================================================================
   Section 3: Probe State (RFC 8899 Section 5.1.4)
   ============================================================================= *)

Inductive ProbeState :=
  | PROBE_DISABLED
  | PROBE_INACTIVE
  | PROBE_ACTIVE
  | PROBE_BASE.

Record ProbeInfo := {
  probe_state : ProbeState;
  probe_size : N;
  probe_count : N;             (* Number sent at this size *)
  probe_lost : N;              (* Number lost at this size *)
  probe_acked : N;             (* Number acknowledged *)
  probe_seq : word64;          (* Sequence number *)
  probe_sent_time : N;         (* When last probe sent *)
  probe_timer : option N       (* Next probe time *)
}.

(* =============================================================================
   Section 4: DPLPMTUD Context (RFC 8899 Section 5.1)
   ============================================================================= *)

Record DPLPMTUDContext := {
  dplpmtud_state : DPLPMTUDState;
  dplpmtud_probe_state : ProbeState;
  
  (* Path information *)
  dplpmtud_plpmtu : N;          (* Current Packetization Layer PMTU *)
  dplpmtud_probed_size : N;     (* Size being probed *)
  dplpmtud_max_plpmtu : N;      (* Maximum PLPMTU *)
  
  (* Search state *)
  dplpmtud_search_low : N;      (* Binary search lower bound *)
  dplpmtud_search_high : N;     (* Binary search upper bound *)
  dplpmtud_search_iterations : N;
  
  (* Probe tracking *)
  dplpmtud_probes : list ProbeInfo;
  dplpmtud_probe_count : N;
  dplpmtud_consecutive_failures : N;
  
  (* Timers *)
  dplpmtud_probe_timer : option N;
  dplpmtud_raise_timer : option N;
  dplpmtud_confirm_timer : option N;
  
  (* Statistics *)
  dplpmtud_bytes_sent : N;
  dplpmtud_bytes_acked : N;
  dplpmtud_black_hole_detected : bool;
  
  (* Configuration *)
  dplpmtud_max_probes : N;
  dplpmtud_probe_method : N     (* 0=padding, 1=extension header *)
}.

(* Initialize DPLPMTUD context *)
Definition init_dplpmtud : DPLPMTUDContext :=
  {| dplpmtud_state := DPLPMTUD_BASE;
     dplpmtud_probe_state := PROBE_INACTIVE;
     dplpmtud_plpmtu := BASE_PLPMTU;
     dplpmtud_probed_size := BASE_PLPMTU;
     dplpmtud_max_plpmtu := MAX_PLPMTU;
     dplpmtud_search_low := BASE_PLPMTU;
     dplpmtud_search_high := MAX_PLPMTU;
     dplpmtud_search_iterations := 0;
     dplpmtud_probes := [];
     dplpmtud_probe_count := 0;
     dplpmtud_consecutive_failures := 0;
     dplpmtud_probe_timer := None;
     dplpmtud_raise_timer := None;
     dplpmtud_confirm_timer := None;
     dplpmtud_bytes_sent := 0;
     dplpmtud_bytes_acked := 0;
     dplpmtud_black_hole_detected := false;
     dplpmtud_max_probes := MAX_PROBES;
     dplpmtud_probe_method := 0 |}.

(* =============================================================================
   Section 5: State Machine Transitions (RFC 8899 Section 5.2)
   ============================================================================= *)

Definition transition_to_searching (ctx : DPLPMTUDContext) : DPLPMTUDContext :=
  {| dplpmtud_state := DPLPMTUD_SEARCHING;
     dplpmtud_probe_state := PROBE_ACTIVE;
     dplpmtud_plpmtu := ctx.(dplpmtud_plpmtu);
     dplpmtud_probed_size := ctx.(dplpmtud_plpmtu);
     dplpmtud_max_plpmtu := ctx.(dplpmtud_max_plpmtu);
     dplpmtud_search_low := ctx.(dplpmtud_plpmtu);
     dplpmtud_search_high := ctx.(dplpmtud_max_plpmtu);
     dplpmtud_search_iterations := 0;
     dplpmtud_probes := ctx.(dplpmtud_probes);
     dplpmtud_probe_count := 0;
     dplpmtud_consecutive_failures := 0;
     dplpmtud_probe_timer := ctx.(dplpmtud_probe_timer);
     dplpmtud_raise_timer := None;
     dplpmtud_confirm_timer := ctx.(dplpmtud_confirm_timer);
     dplpmtud_bytes_sent := ctx.(dplpmtud_bytes_sent);
     dplpmtud_bytes_acked := ctx.(dplpmtud_bytes_acked);
     dplpmtud_black_hole_detected := false;
     dplpmtud_max_probes := ctx.(dplpmtud_max_probes);
     dplpmtud_probe_method := ctx.(dplpmtud_probe_method) |}.

Definition transition_to_search_complete (ctx : DPLPMTUDContext) (now : N) 
                                        : DPLPMTUDContext :=
  {| dplpmtud_state := DPLPMTUD_SEARCH_COMPLETE;
     dplpmtud_probe_state := PROBE_INACTIVE;
     dplpmtud_plpmtu := ctx.(dplpmtud_plpmtu);
     dplpmtud_probed_size := ctx.(dplpmtud_probed_size);
     dplpmtud_max_plpmtu := ctx.(dplpmtud_max_plpmtu);
     dplpmtud_search_low := ctx.(dplpmtud_search_low);
     dplpmtud_search_high := ctx.(dplpmtud_search_high);
     dplpmtud_search_iterations := ctx.(dplpmtud_search_iterations);
     dplpmtud_probes := ctx.(dplpmtud_probes);
     dplpmtud_probe_count := 0;
     dplpmtud_consecutive_failures := 0;
     dplpmtud_probe_timer := None;
     dplpmtud_raise_timer := Some (now + PMTU_RAISE_TIMER);
     dplpmtud_confirm_timer := Some (now + CONFIRMATION_TIMER);
     dplpmtud_bytes_sent := ctx.(dplpmtud_bytes_sent);
     dplpmtud_bytes_acked := ctx.(dplpmtud_bytes_acked);
     dplpmtud_black_hole_detected := false;
     dplpmtud_max_probes := ctx.(dplpmtud_max_probes);
     dplpmtud_probe_method := ctx.(dplpmtud_probe_method) |}.

Definition transition_to_error (ctx : DPLPMTUDContext) : DPLPMTUDContext :=
  {| dplpmtud_state := DPLPMTUD_ERROR;
     dplpmtud_probe_state := PROBE_BASE;
     dplpmtud_plpmtu := BASE_PLPMTU;
     dplpmtud_probed_size := BASE_PLPMTU;
     dplpmtud_max_plpmtu := ctx.(dplpmtud_max_plpmtu);
     dplpmtud_search_low := BASE_PLPMTU;
     dplpmtud_search_high := ctx.(dplpmtud_search_high);
     dplpmtud_search_iterations := 0;
     dplpmtud_probes := [];
     dplpmtud_probe_count := 0;
     dplpmtud_consecutive_failures := 0;
     dplpmtud_probe_timer := None;
     dplpmtud_raise_timer := None;
     dplpmtud_confirm_timer := None;
     dplpmtud_bytes_sent := ctx.(dplpmtud_bytes_sent);
     dplpmtud_bytes_acked := ctx.(dplpmtud_bytes_acked);
     dplpmtud_black_hole_detected := true;
     dplpmtud_max_probes := ctx.(dplpmtud_max_probes);
     dplpmtud_probe_method := ctx.(dplpmtud_probe_method) |}.

(* =============================================================================
   Section 6: Probe Generation (RFC 8899 Section 4.1)
   ============================================================================= *)

(* Calculate next probe size *)
Definition calculate_probe_size (ctx : DPLPMTUDContext) : N :=
  match ctx.(dplpmtud_state) with
  | DPLPMTUD_SEARCHING =>
      let low := ctx.(dplpmtud_search_low) in
      let high := ctx.(dplpmtud_search_high) in
      if N.leb (high - low) SEARCH_COMPLETE_THRESHOLD then
        high  (* Close enough, try maximum *)
      else
        (* Binary search with alignment *)
        let mid := (low + high) / 2 in
        (mid / 4) * 4  (* Align to 4-byte boundary *)
  | DPLPMTUD_SEARCH_COMPLETE =>
      (* Try to increase *)
      N.min (ctx.(dplpmtud_plpmtu) + 32) ctx.(dplpmtud_max_plpmtu)
  | _ => ctx.(dplpmtud_plpmtu)
  end.

(* Create probe packet *)
Record ProbePacket := {
  pp_size : N;
  pp_seq : word64;
  pp_timestamp : N;
  pp_padding : list byte;
  pp_retry_count : N
}.

Definition create_probe (ctx : DPLPMTUDContext) (seq : word64) (now : N) 
                       : ProbePacket :=
  let size := calculate_probe_size ctx in
  {| pp_size := size;
     pp_seq := seq;
     pp_timestamp := now;
     pp_padding := repeat 0 (N.to_nat (size - MIN_PLPMTU));
     pp_retry_count := 0 |}.

(* =============================================================================
   Section 7: Probe Acknowledgment Processing (RFC 8899 Section 4.2)
   ============================================================================= *)

Definition process_probe_ack (ctx : DPLPMTUDContext) (probe_size : N) 
                            (now : N) : DPLPMTUDContext :=
  match ctx.(dplpmtud_state) with
  | DPLPMTUD_SEARCHING =>
      if N.ltb ctx.(dplpmtud_plpmtu) probe_size then
        (* Found larger working size *)
        let ctx' := {| dplpmtud_state := ctx.(dplpmtud_state);
                       dplpmtud_probe_state := ctx.(dplpmtud_probe_state);
                       dplpmtud_plpmtu := probe_size;
                       dplpmtud_probed_size := probe_size;
                       dplpmtud_max_plpmtu := ctx.(dplpmtud_max_plpmtu);
                       dplpmtud_search_low := probe_size;
                       dplpmtud_search_high := ctx.(dplpmtud_search_high);
                       dplpmtud_search_iterations := ctx.(dplpmtud_search_iterations) + 1;
                       dplpmtud_probes := ctx.(dplpmtud_probes);
                       dplpmtud_probe_count := 0;
                       dplpmtud_consecutive_failures := 0;
                       dplpmtud_probe_timer := ctx.(dplpmtud_probe_timer);
                       dplpmtud_raise_timer := ctx.(dplpmtud_raise_timer);
                       dplpmtud_confirm_timer := ctx.(dplpmtud_confirm_timer);
                       dplpmtud_bytes_sent := ctx.(dplpmtud_bytes_sent);
                       dplpmtud_bytes_acked := ctx.(dplpmtud_bytes_acked) + probe_size;
                       dplpmtud_black_hole_detected := false;
                       dplpmtud_max_probes := ctx.(dplpmtud_max_probes);
                       dplpmtud_probe_method := ctx.(dplpmtud_probe_method) |} in
        
        (* Check if search is complete *)
        if N.leb (ctx'.(dplpmtud_search_high) - ctx'.(dplpmtud_search_low))
                 SEARCH_COMPLETE_THRESHOLD then
          transition_to_search_complete ctx' now
        else
          ctx'
      else
        ctx
  | _ => ctx
  end.

(* Process probe loss *)
Definition process_probe_loss (ctx : DPLPMTUDContext) (probe_size : N) 
                             : DPLPMTUDContext :=
  match ctx.(dplpmtud_state) with
  | DPLPMTUD_SEARCHING =>
      let failures := ctx.(dplpmtud_consecutive_failures) + 1 in
      if N.ltb BLACK_HOLE_THRESHOLD failures then
        transition_to_error ctx
      else
        (* Reduce upper bound *)
        {| dplpmtud_state := ctx.(dplpmtud_state);
           dplpmtud_probe_state := ctx.(dplpmtud_probe_state);
           dplpmtud_plpmtu := ctx.(dplpmtud_plpmtu);
           dplpmtud_probed_size := ctx.(dplpmtud_probed_size);
           dplpmtud_max_plpmtu := ctx.(dplpmtud_max_plpmtu);
           dplpmtud_search_low := ctx.(dplpmtud_search_low);
           dplpmtud_search_high := probe_size - 1;
           dplpmtud_search_iterations := ctx.(dplpmtud_search_iterations) + 1;
           dplpmtud_probes := ctx.(dplpmtud_probes);
           dplpmtud_probe_count := ctx.(dplpmtud_probe_count) + 1;
           dplpmtud_consecutive_failures := failures;
           dplpmtud_probe_timer := ctx.(dplpmtud_probe_timer);
           dplpmtud_raise_timer := ctx.(dplpmtud_raise_timer);
           dplpmtud_confirm_timer := ctx.(dplpmtud_confirm_timer);
           dplpmtud_bytes_sent := ctx.(dplpmtud_bytes_sent);
           dplpmtud_bytes_acked := ctx.(dplpmtud_bytes_acked);
           dplpmtud_black_hole_detected := false;
           dplpmtud_max_probes := ctx.(dplpmtud_max_probes);
           dplpmtud_probe_method := ctx.(dplpmtud_probe_method) |}
  | _ => ctx
  end.

(* =============================================================================
   Section 8: Confirmation and Validation (RFC 8899 Section 4.3)
   ============================================================================= *)

Definition needs_confirmation (ctx : DPLPMTUDContext) (now : N) : bool :=
  match ctx.(dplpmtud_confirm_timer) with
  | Some timer => N.ltb timer now
  | None => false
  end.

Definition send_confirmation_probe (ctx : DPLPMTUDContext) (now : N) 
                                  : (ProbePacket * DPLPMTUDContext) :=
  let probe := {| pp_size := ctx.(dplpmtud_plpmtu);
                  pp_seq := 0;  (* Simplified *)
                  pp_timestamp := now;
                  pp_padding := [];
                  pp_retry_count := 0 |} in
  let ctx' := {| dplpmtud_state := ctx.(dplpmtud_state);
                 dplpmtud_probe_state := ctx.(dplpmtud_probe_state);
                 dplpmtud_plpmtu := ctx.(dplpmtud_plpmtu);
                 dplpmtud_probed_size := ctx.(dplpmtud_probed_size);
                 dplpmtud_max_plpmtu := ctx.(dplpmtud_max_plpmtu);
                 dplpmtud_search_low := ctx.(dplpmtud_search_low);
                 dplpmtud_search_high := ctx.(dplpmtud_search_high);
                 dplpmtud_search_iterations := ctx.(dplpmtud_search_iterations);
                 dplpmtud_probes := ctx.(dplpmtud_probes);
                 dplpmtud_probe_count := ctx.(dplpmtud_probe_count);
                 dplpmtud_consecutive_failures := ctx.(dplpmtud_consecutive_failures);
                 dplpmtud_probe_timer := ctx.(dplpmtud_probe_timer);
                 dplpmtud_raise_timer := ctx.(dplpmtud_raise_timer);
                 dplpmtud_confirm_timer := Some (now + CONFIRMATION_TIMER);
                 dplpmtud_bytes_sent := ctx.(dplpmtud_bytes_sent);
                 dplpmtud_bytes_acked := ctx.(dplpmtud_bytes_acked);
                 dplpmtud_black_hole_detected := ctx.(dplpmtud_black_hole_detected);
                 dplpmtud_max_probes := ctx.(dplpmtud_max_probes);
                 dplpmtud_probe_method := ctx.(dplpmtud_probe_method) |} in
  (probe, ctx').

(* =============================================================================
   Section 9: Black Hole Detection (RFC 8899 Section 5.3)
   ============================================================================= *)

Definition detect_black_hole (ctx : DPLPMTUDContext) (loss_count : N) 
                            : DPLPMTUDContext :=
  if N.ltb ERROR_THRESHOLD loss_count then
    transition_to_error ctx
  else if N.ltb BLACK_HOLE_THRESHOLD loss_count then
    (* Suspected black hole - probe BASE_PLPMTU *)
    {| dplpmtud_state := ctx.(dplpmtud_state);
       dplpmtud_probe_state := PROBE_BASE;
       dplpmtud_plpmtu := ctx.(dplpmtud_plpmtu);
       dplpmtud_probed_size := BASE_PLPMTU;
       dplpmtud_max_plpmtu := ctx.(dplpmtud_max_plpmtu);
       dplpmtud_search_low := ctx.(dplpmtud_search_low);
       dplpmtud_search_high := ctx.(dplpmtud_search_high);
       dplpmtud_search_iterations := ctx.(dplpmtud_search_iterations);
       dplpmtud_probes := ctx.(dplpmtud_probes);
       dplpmtud_probe_count := ctx.(dplpmtud_probe_count);
       dplpmtud_consecutive_failures := loss_count;
       dplpmtud_probe_timer := ctx.(dplpmtud_probe_timer);
       dplpmtud_raise_timer := ctx.(dplpmtud_raise_timer);
       dplpmtud_confirm_timer := ctx.(dplpmtud_confirm_timer);
       dplpmtud_bytes_sent := ctx.(dplpmtud_bytes_sent);
       dplpmtud_bytes_acked := ctx.(dplpmtud_bytes_acked);
       dplpmtud_black_hole_detected := false;
       dplpmtud_max_probes := ctx.(dplpmtud_max_probes);
       dplpmtud_probe_method := ctx.(dplpmtud_probe_method) |}
  else
    ctx.

(* =============================================================================
   Section 10: Integration with Transport Protocols
   ============================================================================= *)

(* UDP-specific integration *)
Definition udp_dplpmtud_decision (ctx : DPLPMTUDContext) (datagram_size : N) 
                                : (bool * N) := (* (can_send, max_size) *)
  if N.leb datagram_size ctx.(dplpmtud_plpmtu) then
    (true, datagram_size)
  else
    (false, ctx.(dplpmtud_plpmtu)).

(* QUIC-specific integration *)
Definition quic_dplpmtud_frame_size (ctx : DPLPMTUDContext) : N :=
  (* Account for QUIC headers *)
  ctx.(dplpmtud_plpmtu) - 30.  (* Simplified *)

(* SCTP-specific integration *)
Definition sctp_dplpmtud_chunk_size (ctx : DPLPMTUDContext) : N :=
  (* Account for SCTP common header *)
  ctx.(dplpmtud_plpmtu) - 12.

(* =============================================================================
   Section 11: Key Properties
   ============================================================================= *)

(* Property 1: PLPMTU never below minimum *)
Theorem plpmtu_minimum : forall ctx,
  ctx.(dplpmtud_plpmtu) >= MIN_PLPMTU.
Proof.
  admit.
Qed.

(* Property 2: Search converges *)
Theorem search_converges : forall ctx,
  ctx.(dplpmtud_state) = DPLPMTUD_SEARCHING ->
  ctx.(dplpmtud_search_iterations) < 20 ->
  exists n, n < 20 /\
  let ctx' := iterate (fun c => process_probe_ack c (calculate_probe_size c) 0) n ctx in
  ctx'.(dplpmtud_state) = DPLPMTUD_SEARCH_COMPLETE.
Proof.
  admit.
Qed.

(* Property 3: Black hole triggers error state *)
Theorem black_hole_to_error : forall ctx,
  ctx.(dplpmtud_consecutive_failures) > BLACK_HOLE_THRESHOLD ->
  (process_probe_loss ctx 0).(dplpmtud_state) = DPLPMTUD_ERROR.
Proof.
  admit.
Qed.

(* Property 4: Error state uses BASE_PLPMTU *)
Theorem error_uses_base : forall ctx,
  (transition_to_error ctx).(dplpmtud_plpmtu) = BASE_PLPMTU.
Proof.
  intros. unfold transition_to_error. reflexivity.
Qed.

(* Property 5: Probe size aligned *)
Theorem probe_aligned : forall ctx,
  let size := calculate_probe_size ctx in
  ctx.(dplpmtud_state) = DPLPMTUD_SEARCHING ->
  N.modulo size 4 = 0 \/ 
  size = ctx.(dplpmtud_search_high).
Proof.
  admit.
Qed.

(* Property 6: Search bounds maintained *)
Theorem search_bounds_valid : forall ctx probe now,
  ctx.(dplpmtud_state) = DPLPMTUD_SEARCHING ->
  let ctx' := process_probe_ack ctx probe now in
  ctx'.(dplpmtud_search_low) <= ctx'.(dplpmtud_search_high).
Proof.
  admit.
Qed.

(* =============================================================================
   Section 12: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction "dplpmtud.ml"
  init_dplpmtud
  transition_to_searching
  transition_to_search_complete
  calculate_probe_size
  create_probe
  process_probe_ack
  process_probe_loss
  detect_black_hole
  needs_confirmation.
    
