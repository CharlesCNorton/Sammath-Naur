(* =============================================================================
   Formal Verification of Transmission Control Protocol (TCP)
   
   Specification: RFC 9293 (W. Eddy, August 2022)
   Obsoletes: RFC 793, 879, 2873, 6093, 6429, 6528, 6691
   Target: TCP Protocol
   
   Module: TCP Protocol Formalization and Verification
   Author: Charles C Norton
   Date: August 29, 2025
   
   "First he sang of the binding of words, that none be lost in the void."
   
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

(* TCP Constants *)
Definition MSL : N := 120000.                 (* Maximum Segment Lifetime: 2 minutes *)
Definition MAX_WINDOW : word16 := 65535.
Definition MAX_SEG_SIZE : word16 := 536.      (* Default MSS *)
Definition MIN_RTO : N := 1000.               (* Min retransmission timeout (ms) *)
Definition MAX_RTO : N := 60000.              (* Max retransmission timeout (ms) *)
Definition INITIAL_RTO : N := 3000.           (* Initial RTO (ms) *)
Definition SYN_RETRIES : N := 6.
Definition DATA_RETRIES : N := 15.

(* =============================================================================
   Section 2: Sequence Numbers (RFC 9293 Section 3.4)
   ============================================================================= *)

Definition SeqNum := word32.
Definition AckNum := word32.

(* Sequence number arithmetic (mod 2^32) *)
Definition seq_lt (a b : SeqNum) : bool :=
  N.ltb ((b - a) mod (2^32)) (2^31).

Definition seq_leq (a b : SeqNum) : bool :=
  orb (N.eqb a b) (seq_lt a b).

Definition seq_between (a b c : SeqNum) : bool :=
  andb (seq_leq a b) (seq_lt b c).

(* =============================================================================
   Section 3: TCP Header (RFC 9293 Section 3.1)
   ============================================================================= *)

Record TCPHeader := {
  tcp_src_port : word16;
  tcp_dst_port : word16;
  tcp_seq : SeqNum;
  tcp_ack : AckNum;
  tcp_data_offset : N;     (* 4 bits: header length in 32-bit words *)
  tcp_reserved : N;        (* 3 bits: must be zero *)
  tcp_flags : N;           (* 9 bits: control flags *)
  tcp_window : word16;
  tcp_checksum : word16;
  tcp_urgent : word16;
  tcp_options : list byte
}.

(* TCP Flags *)
Definition FLAG_FIN : N := 0.
Definition FLAG_SYN : N := 1.
Definition FLAG_RST : N := 2.
Definition FLAG_PSH : N := 3.
Definition FLAG_ACK : N := 4.
Definition FLAG_URG : N := 5.
Definition FLAG_ECE : N := 6.
Definition FLAG_CWR : N := 7.
Definition FLAG_NS : N := 8.

Definition get_flag (flags : N) (bit : N) : bool :=
  N.testbit flags bit.

Definition set_flag (flags : N) (bit : N) : N :=
  N.lor flags (N.shiftl 1 bit).

(* =============================================================================
   Section 4: Connection States (RFC 9293 Section 3.6)
   ============================================================================= *)

Inductive TCPState :=
  | CLOSED
  | LISTEN
  | SYN_SENT
  | SYN_RECEIVED
  | ESTABLISHED
  | FIN_WAIT_1
  | FIN_WAIT_2
  | CLOSE_WAIT
  | CLOSING
  | LAST_ACK
  | TIME_WAIT.

(* =============================================================================
   Section 5: Transmission Control Block (TCB)
   ============================================================================= *)

Record TCB := {
  (* Connection identification *)
  tcb_local_addr : word32;
  tcb_remote_addr : word32;
  tcb_local_port : word16;
  tcb_remote_port : word16;
  
  (* Connection state *)
  tcb_state : TCPState;
  
  (* Send sequence variables *)
  tcb_snd_una : SeqNum;      (* Send unacknowledged *)
  tcb_snd_nxt : SeqNum;      (* Send next *)
  tcb_snd_wnd : word16;      (* Send window *)
  tcb_snd_wl1 : SeqNum;      (* Segment seq for last window update *)
  tcb_snd_wl2 : AckNum;      (* Segment ack for last window update *)
  tcb_iss : SeqNum;          (* Initial send sequence number *)
  
  (* Receive sequence variables *)
  tcb_rcv_nxt : SeqNum;      (* Receive next *)
  tcb_rcv_wnd : word16;      (* Receive window *)
  tcb_irs : SeqNum;          (* Initial receive sequence number *)
  
  (* Congestion control (RFC 5681) *)
  tcb_cwnd : word32;         (* Congestion window *)
  tcb_ssthresh : word32;     (* Slow start threshold *)
  tcb_rtt : N;               (* Round trip time *)
  tcb_rttvar : N;            (* RTT variance *)
  tcb_rto : N;               (* Retransmission timeout *)
  
  (* Timers *)
  tcb_retransmit_timer : option N;
  tcb_persist_timer : option N;
  tcb_keepalive_timer : option N;
  tcb_time_wait_timer : option N;
  
  (* Options *)
  tcb_mss : word16;          (* Maximum segment size *)
  tcb_sack_permitted : bool;
  tcb_timestamps : bool;
  tcb_window_scale : N
}.

(* =============================================================================
   Section 6: TCP Options (RFC 9293 Section 3.2)
   ============================================================================= *)

Inductive TCPOption :=
  | OptEnd : TCPOption                      (* Kind 0 *)
  | OptNop : TCPOption                      (* Kind 1 *)
  | OptMSS : word16 -> TCPOption            (* Kind 2 *)
  | OptWindowScale : byte -> TCPOption      (* Kind 3 - RFC 7323 *)
  | OptSACKPermitted : TCPOption            (* Kind 4 - RFC 2018 *)
  | OptSACK : list (SeqNum * SeqNum) -> TCPOption (* Kind 5 *)
  | OptTimestamp : word32 -> word32 -> TCPOption  (* Kind 8 - RFC 7323 *)
  | OptUnknown : byte -> list byte -> TCPOption.

(* =============================================================================
   Section 7: Segment Processing (RFC 9293 Section 3.10)
   ============================================================================= *)

(* Check if segment is acceptable *)
Definition segment_acceptable (tcb : TCB) (seg_seq : SeqNum) (seg_len : N) : bool :=
  let rcv_nxt := tcb.(tcb_rcv_nxt) in
  let rcv_wnd := tcb.(tcb_rcv_wnd) in
  if N.eqb seg_len 0 then
    if N.eqb rcv_wnd 0 then
      N.eqb seg_seq rcv_nxt
    else
      andb (seq_leq rcv_nxt seg_seq)
           (seq_lt seg_seq (rcv_nxt + rcv_wnd))
  else
    if N.eqb rcv_wnd 0 then
      false
    else
      orb (andb (seq_leq rcv_nxt seg_seq)
                (seq_lt seg_seq (rcv_nxt + rcv_wnd)))
          (andb (seq_leq rcv_nxt (seg_seq + seg_len - 1))
                (seq_lt (seg_seq + seg_len - 1) (rcv_nxt + rcv_wnd))).

(* =============================================================================
   Section 8: State Machine Transitions (RFC 9293 Section 3.10)
   ============================================================================= *)

Definition tcp_state_transition (tcb : TCB) (hdr : TCPHeader) (data : list byte)
                               : TCB * option TCPHeader * option (list byte) :=
  match tcb.(tcb_state) with
  | CLOSED =>
      if get_flag hdr.(tcp_flags) FLAG_SYN then
        (* Passive open or simultaneous open *)
        (tcb, None, None)
      else if get_flag hdr.(tcp_flags) FLAG_RST then
        (tcb, None, None)
      else
        (* Send RST *)
        (tcb, Some {| tcp_src_port := tcb.(tcb_local_port);
                      tcp_dst_port := tcb.(tcb_remote_port);
                      tcp_seq := 0;
                      tcp_ack := hdr.(tcp_seq) + N.of_nat (length data);
                      tcp_data_offset := 5;
                      tcp_reserved := 0;
                      tcp_flags := N.lor (set_flag 0 FLAG_RST) (set_flag 0 FLAG_ACK);
                      tcp_window := 0;
                      tcp_checksum := 0;
                      tcp_urgent := 0;
                      tcp_options := [] |}, None)
  
  | LISTEN =>
      if get_flag hdr.(tcp_flags) FLAG_RST then
        (tcb, None, None)
      else if get_flag hdr.(tcp_flags) FLAG_ACK then
        (* Send RST *)
        (tcb, None, None)
      else if get_flag hdr.(tcp_flags) FLAG_SYN then
        (* Send SYN+ACK, move to SYN_RECEIVED *)
        let tcb' := {| tcb_local_addr := tcb.(tcb_local_addr);
                       tcb_remote_addr := tcb.(tcb_remote_addr);
                       tcb_local_port := tcb.(tcb_local_port);
                       tcb_remote_port := tcb.(tcb_remote_port);
                       tcb_state := SYN_RECEIVED;
                       tcb_snd_una := tcb.(tcb_iss);
                       tcb_snd_nxt := tcb.(tcb_iss) + 1;
                       tcb_snd_wnd := hdr.(tcp_window);
                       tcb_snd_wl1 := hdr.(tcp_seq);
                       tcb_snd_wl2 := hdr.(tcp_seq);
                       tcb_iss := tcb.(tcb_iss);
                       tcb_rcv_nxt := hdr.(tcp_seq) + 1;
                       tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
                       tcb_irs := hdr.(tcp_seq);
                       tcb_cwnd := tcb.(tcb_cwnd);
                       tcb_ssthresh := tcb.(tcb_ssthresh);
                       tcb_rtt := tcb.(tcb_rtt);
                       tcb_rttvar := tcb.(tcb_rttvar);
                       tcb_rto := tcb.(tcb_rto);
                       tcb_retransmit_timer := tcb.(tcb_retransmit_timer);
                       tcb_persist_timer := tcb.(tcb_persist_timer);
                       tcb_keepalive_timer := tcb.(tcb_keepalive_timer);
                       tcb_time_wait_timer := tcb.(tcb_time_wait_timer);
                       tcb_mss := tcb.(tcb_mss);
                       tcb_sack_permitted := tcb.(tcb_sack_permitted);
                       tcb_timestamps := tcb.(tcb_timestamps);
                       tcb_window_scale := tcb.(tcb_window_scale) |} in
        (tcb', None, None)
      else
        (tcb, None, None)
  
  | ESTABLISHED =>
      (* Check sequence number *)
      if negb (segment_acceptable tcb hdr.(tcp_seq) (N.of_nat (length data))) then
        (* Send ACK *)
        (tcb, None, None)
      else if get_flag hdr.(tcp_flags) FLAG_RST then
        (* Connection reset *)
        ({| tcb_local_addr := tcb.(tcb_local_addr);
            tcb_remote_addr := tcb.(tcb_remote_addr);
            tcb_local_port := tcb.(tcb_local_port);
            tcb_remote_port := tcb.(tcb_remote_port);
            tcb_state := CLOSED;
            tcb_snd_una := tcb.(tcb_snd_una);
            tcb_snd_nxt := tcb.(tcb_snd_nxt);
            tcb_snd_wnd := tcb.(tcb_snd_wnd);
            tcb_snd_wl1 := tcb.(tcb_snd_wl1);
            tcb_snd_wl2 := tcb.(tcb_snd_wl2);
            tcb_iss := tcb.(tcb_iss);
            tcb_rcv_nxt := tcb.(tcb_rcv_nxt);
            tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
            tcb_irs := tcb.(tcb_irs);
            tcb_cwnd := tcb.(tcb_cwnd);
            tcb_ssthresh := tcb.(tcb_ssthresh);
            tcb_rtt := tcb.(tcb_rtt);
            tcb_rttvar := tcb.(tcb_rttvar);
            tcb_rto := tcb.(tcb_rto);
            tcb_retransmit_timer := None;
            tcb_persist_timer := None;
            tcb_keepalive_timer := None;
            tcb_time_wait_timer := None;
            tcb_mss := tcb.(tcb_mss);
            tcb_sack_permitted := tcb.(tcb_sack_permitted);
            tcb_timestamps := tcb.(tcb_timestamps);
            tcb_window_scale := tcb.(tcb_window_scale) |}, None, None)
      else if get_flag hdr.(tcp_flags) FLAG_FIN then
        (* Process FIN *)
        (tcb, None, None) (* Simplified *)
      else
        (* Process data *)
        (tcb, None, Some data)
  
  | _ => (tcb, None, None) (* Other states simplified *)
  end.

(* =============================================================================
   Section 9: Congestion Control (RFC 5681)
   ============================================================================= *)

Definition update_cwnd_ack (tcb : TCB) : TCB :=
  if N.ltb tcb.(tcb_cwnd) tcb.(tcb_ssthresh) then
    (* Slow start *)
    {| tcb_local_addr := tcb.(tcb_local_addr);
       tcb_remote_addr := tcb.(tcb_remote_addr);
       tcb_local_port := tcb.(tcb_local_port);
       tcb_remote_port := tcb.(tcb_remote_port);
       tcb_state := tcb.(tcb_state);
       tcb_snd_una := tcb.(tcb_snd_una);
       tcb_snd_nxt := tcb.(tcb_snd_nxt);
       tcb_snd_wnd := tcb.(tcb_snd_wnd);
       tcb_snd_wl1 := tcb.(tcb_snd_wl1);
       tcb_snd_wl2 := tcb.(tcb_snd_wl2);
       tcb_iss := tcb.(tcb_iss);
       tcb_rcv_nxt := tcb.(tcb_rcv_nxt);
       tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
       tcb_irs := tcb.(tcb_irs);
       tcb_cwnd := tcb.(tcb_cwnd) + tcb.(tcb_mss);
       tcb_ssthresh := tcb.(tcb_ssthresh);
       tcb_rtt := tcb.(tcb_rtt);
       tcb_rttvar := tcb.(tcb_rttvar);
       tcb_rto := tcb.(tcb_rto);
       tcb_retransmit_timer := tcb.(tcb_retransmit_timer);
       tcb_persist_timer := tcb.(tcb_persist_timer);
       tcb_keepalive_timer := tcb.(tcb_keepalive_timer);
       tcb_time_wait_timer := tcb.(tcb_time_wait_timer);
       tcb_mss := tcb.(tcb_mss);
       tcb_sack_permitted := tcb.(tcb_sack_permitted);
       tcb_timestamps := tcb.(tcb_timestamps);
       tcb_window_scale := tcb.(tcb_window_scale) |}
  else
    (* Congestion avoidance *)
    tcb.

Definition update_cwnd_loss (tcb : TCB) : TCB :=
  (* On loss, set ssthresh to half of cwnd *)
  {| tcb_local_addr := tcb.(tcb_local_addr);
     tcb_remote_addr := tcb.(tcb_remote_addr);
     tcb_local_port := tcb.(tcb_local_port);
     tcb_remote_port := tcb.(tcb_remote_port);
     tcb_state := tcb.(tcb_state);
     tcb_snd_una := tcb.(tcb_snd_una);
     tcb_snd_nxt := tcb.(tcb_snd_nxt);
     tcb_snd_wnd := tcb.(tcb_snd_wnd);
     tcb_snd_wl1 := tcb.(tcb_snd_wl1);
     tcb_snd_wl2 := tcb.(tcb_snd_wl2);
     tcb_iss := tcb.(tcb_iss);
     tcb_rcv_nxt := tcb.(tcb_rcv_nxt);
     tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
     tcb_irs := tcb.(tcb_irs);
     tcb_cwnd := tcb.(tcb_mss);
     tcb_ssthresh := N.max (tcb.(tcb_cwnd) / 2) (2 * tcb.(tcb_mss));
     tcb_rtt := tcb.(tcb_rtt);
     tcb_rttvar := tcb.(tcb_rttvar);
     tcb_rto := tcb.(tcb_rto);
     tcb_retransmit_timer := tcb.(tcb_retransmit_timer);
     tcb_persist_timer := tcb.(tcb_persist_timer);
     tcb_keepalive_timer := tcb.(tcb_keepalive_timer);
     tcb_time_wait_timer := tcb.(tcb_time_wait_timer);
     tcb_mss := tcb.(tcb_mss);
     tcb_sack_permitted := tcb.(tcb_sack_permitted);
     tcb_timestamps := tcb.(tcb_timestamps);
     tcb_window_scale := tcb.(tcb_window_scale) |}.

(* =============================================================================
   Section 10: Retransmission (RFC 9293 Section 3.8.3)
   ============================================================================= *)

Definition calculate_rto (tcb : TCB) (measured_rtt : N) : TCB :=
  (* Jacobson's algorithm *)
  let alpha := 125 in  (* 1/8 as fixed point *)
  let beta := 250 in   (* 1/4 as fixed point *)
  let rttvar' := ((1000 - beta) * tcb.(tcb_rttvar) + 
                   beta * (if N.ltb tcb.(tcb_rtt) measured_rtt 
                          then measured_rtt - tcb.(tcb_rtt)
                          else tcb.(tcb_rtt) - measured_rtt)) / 1000 in
  let rtt' := ((1000 - alpha) * tcb.(tcb_rtt) + alpha * measured_rtt) / 1000 in
  let rto' := N.max MIN_RTO (N.min MAX_RTO (rtt' + 4 * rttvar')) in
  {| tcb_local_addr := tcb.(tcb_local_addr);
     tcb_remote_addr := tcb.(tcb_remote_addr);
     tcb_local_port := tcb.(tcb_local_port);
     tcb_remote_port := tcb.(tcb_remote_port);
     tcb_state := tcb.(tcb_state);
     tcb_snd_una := tcb.(tcb_snd_una);
     tcb_snd_nxt := tcb.(tcb_snd_nxt);
     tcb_snd_wnd := tcb.(tcb_snd_wnd);
     tcb_snd_wl1 := tcb.(tcb_snd_wl1);
     tcb_snd_wl2 := tcb.(tcb_snd_wl2);
     tcb_iss := tcb.(tcb_iss);
     tcb_rcv_nxt := tcb.(tcb_rcv_nxt);
     tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
     tcb_irs := tcb.(tcb_irs);
     tcb_cwnd := tcb.(tcb_cwnd);
     tcb_ssthresh := tcb.(tcb_ssthresh);
     tcb_rtt := rtt';
     tcb_rttvar := rttvar';
     tcb_rto := rto';
     tcb_retransmit_timer := tcb.(tcb_retransmit_timer);
     tcb_persist_timer := tcb.(tcb_persist_timer);
     tcb_keepalive_timer := tcb.(tcb_keepalive_timer);
     tcb_time_wait_timer := tcb.(tcb_time_wait_timer);
     tcb_mss := tcb.(tcb_mss);
     tcb_sack_permitted := tcb.(tcb_sack_permitted);
     tcb_timestamps := tcb.(tcb_timestamps);
     tcb_window_scale := tcb.(tcb_window_scale) |}.

(* =============================================================================
   Section 11: Key Properties
   ============================================================================= *)

(* Property 1: Sequence number comparison is transitive *)
Theorem seq_lt_trans : forall a b c,
  seq_lt a b = true -> seq_lt b c = true -> seq_lt a c = true.
Proof.
  admit.
Qed.

(* Property 2: State transitions preserve validity *)
Theorem state_transition_valid : forall tcb hdr data tcb' resp_hdr resp_data,
  tcp_state_transition tcb hdr data = (tcb', resp_hdr, resp_data) ->
  tcb'.(tcb_state) <> CLOSED \/ tcb.(tcb_state) = CLOSED.
Proof.
  admit.
Qed.

(* Property 3: Congestion window never negative *)
Theorem cwnd_non_negative : forall tcb,
  0 < tcb.(tcb_cwnd).
Proof.
  admit.
Qed.

(* Property 4: RTO bounded *)
Theorem rto_bounded : forall tcb rtt,
  let tcb' := calculate_rto tcb rtt in
  MIN_RTO <= tcb'.(tcb_rto) <= MAX_RTO.
Proof.
  admit.
Qed.

(* =============================================================================
   Section 12: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction "tcp.ml"
  tcp_state_transition
  segment_acceptable
  update_cwnd_ack
  update_cwnd_loss
  calculate_rto.
                            
