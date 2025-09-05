(* =============================================================================
   Formal Verification of Transmission Control Protocol (TCP)
   
   Specification: RFC 9293 (W. Eddy, August 2022)
   Obsoletes: RFC 793, 879, 2873, 6093, 6429, 6528, 6691
   Target: TCP Protocol - Complete Core Specification
   
   Module: TCP Protocol Formalization and Verification
   Author: Charles C Norton
   Date: September 4, 2025
   
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

(* TCP Constants (units documented inline) *)
Definition MSL : N := 120000.                 (* ms; 2 minutes *)
Definition MAX_WINDOW : word16 := 65535.
Definition DEFAULT_MSS : word16 := 536.       (* octets *)
Definition MIN_RTO : N := 1000.               (* ms *)
Definition MAX_RTO : N := 60000.              (* ms *)
Definition INITIAL_RTO : N := 3000.           (* ms *)
Definition MIN_HEADER_SIZE : N := 20.         (* bytes *)
Definition MAX_HEADER_SIZE : N := 60.         (* bytes *)

(* Congestion Control Constants *)
Definition INITIAL_CWND : N := 10 * DEFAULT_MSS.  (* RFC 6928 *)
Definition INITIAL_SSTHRESH : N := 65535.         (* RFC 5681 *)
Definition MIN_CWND : N := 2 * DEFAULT_MSS.       (* RFC 5681 *)

(* =============================================================================
   Section 2: Sequence Numbers (RFC 9293 Section 3.4)
   ============================================================================= *)

Definition SeqNum := word32.
Definition AckNum := word32.

Definition SEQ_MOD : N := 2^32.
Definition SEQ_HALF : N := 2^31.

Definition seq_add (a : SeqNum) (b : N) : SeqNum := (a + b) mod SEQ_MOD.
Definition seq_sub (a : SeqNum) (b : N) : SeqNum := (a - b + SEQ_MOD) mod SEQ_MOD.

Definition seq_lt (a b : SeqNum) : bool := N.ltb ((b - a) mod SEQ_MOD) SEQ_HALF.
Definition seq_leq (a b : SeqNum) : bool := orb (N.eqb a b) (seq_lt a b).
Definition seq_gt (a b : SeqNum) : bool := seq_lt b a.
Definition seq_geq (a b : SeqNum) : bool := orb (N.eqb a b) (seq_gt a b).

Definition seq_between (a b c : SeqNum) : bool := andb (seq_leq a b) (seq_lt b c).

(* =============================================================================
   Section 3: TCP Header (RFC 9293 Section 3.1)
   ============================================================================= *)

Record TCPHeader := {
  tcp_src_port : word16;
  tcp_dst_port : word16;
  tcp_seq : SeqNum;
  tcp_ack : AckNum;
  tcp_data_offset : N;     (* 4 bits: header size in 32-bit words *)
  tcp_reserved : N;        (* 3 bits: must be zero *)
  tcp_flags : N;           (* 9 bits: NS,CWR,ECE,URG,ACK,PSH,RST,SYN,FIN *)
  tcp_window : word16;
  tcp_checksum : word16;
  tcp_urgent : word16;
  tcp_options : list byte
}.

(* Flags bit positions *)
Definition FLAG_FIN : N := 0.
Definition FLAG_SYN : N := 1.
Definition FLAG_RST : N := 2.
Definition FLAG_PSH : N := 3.
Definition FLAG_ACK : N := 4.
Definition FLAG_URG : N := 5.
Definition FLAG_ECE : N := 6.
Definition FLAG_CWR : N := 7.
Definition FLAG_NS  : N := 8.

Definition get_flag (flags : N) (bit : N) : bool := N.testbit flags bit.
Definition set_flag (flags : N) (bit : N) : N := N.lor flags (N.shiftl 1 bit).

Definition is_syn_segment (hdr : TCPHeader) : bool := get_flag hdr.(tcp_flags) FLAG_SYN.
Definition is_fin_segment (hdr : TCPHeader) : bool := get_flag hdr.(tcp_flags) FLAG_FIN.
Definition is_rst_segment (hdr : TCPHeader) : bool := get_flag hdr.(tcp_flags) FLAG_RST.
Definition is_ack_segment (hdr : TCPHeader) : bool := get_flag hdr.(tcp_flags) FLAG_ACK.
Definition is_psh_segment (hdr : TCPHeader) : bool := get_flag hdr.(tcp_flags) FLAG_PSH.

(* Basic structural validation for headers per RFC 9293 Section 3.1 *)
Definition header_length_bytes (hdr : TCPHeader) : N := hdr.(tcp_data_offset) * 4.

Definition valid_header (hdr : TCPHeader) : bool :=
  let hlen := header_length_bytes hdr in
  let opt_len := N.of_nat (length hdr.(tcp_options)) in
  let expected_hlen := MIN_HEADER_SIZE + opt_len in
  andb (N.leb MIN_HEADER_SIZE hlen)
  (andb (N.leb hlen MAX_HEADER_SIZE)
  (andb (N.eqb hlen expected_hlen)
  (andb (N.eqb (hdr.(tcp_reserved)) 0)
        true))).

(* =============================================================================
   Section 4: Connection States (RFC 9293 Section 3.6)
   ============================================================================= *)

Inductive TCPState :=
  | CLOSED | LISTEN | SYN_SENT | SYN_RECEIVED | ESTABLISHED
  | FIN_WAIT_1 | FIN_WAIT_2 | CLOSE_WAIT | CLOSING | LAST_ACK | TIME_WAIT.

Definition is_synchronized (st : TCPState) : bool :=
  match st with
  | ESTABLISHED | FIN_WAIT_1 | FIN_WAIT_2 | CLOSE_WAIT | CLOSING | LAST_ACK | TIME_WAIT => true
  | _ => false
  end.

(* =============================================================================
   Section 5: Retransmission Queue Entry
   ============================================================================= *)

Record RetransmitEntry := {
  re_seq : SeqNum;
  re_len : N;
  re_data : list byte;
  re_timestamp : N;
  re_retrans_count : N
}.

(* =============================================================================
   Section 6: Transmission Control Block (TCB) - Enhanced
   ============================================================================= *)

Record ReassemblyRange := { rr_start : SeqNum; rr_len : N }.

Record TCB := {
  (* Identification *)
  tcb_local_addr : word32;
  tcb_remote_addr : word32;
  tcb_local_port : word16;
  tcb_remote_port : word16;

  (* State *)
  tcb_state : TCPState;

  (* Send sequence variables *)
  tcb_snd_una : SeqNum;   (* unacked *)
  tcb_snd_nxt : SeqNum;   (* next to send *)
  tcb_snd_wnd : word16;   (* send window (advertised by peer) *)
  tcb_snd_up  : SeqNum;   (* urgent pointer *)
  tcb_snd_wl1 : SeqNum;   (* seg.seq for last window update *)
  tcb_snd_wl2 : AckNum;   (* seg.ack for last window update *)
  tcb_iss     : SeqNum;   (* initial send seq *)

  (* Receive sequence variables *)
  tcb_rcv_nxt : SeqNum;   (* next seq expected *)
  tcb_rcv_wnd : word16;   (* receive window we advertise *)
  tcb_rcv_up  : SeqNum;   (* urgent pointer *)
  tcb_irs     : SeqNum;   (* initial receive seq *)

  (* Reassembly queue (out-of-order ranges) *)
  tcb_rcv_queue : list ReassemblyRange;

  (* Retransmission queue *)
  tcb_retrans_queue : list RetransmitEntry;

  (* Congestion control variables (RFC 5681 MUST-19) *)
  tcb_cwnd : N;           (* congestion window *)
  tcb_ssthresh : N;       (* slow start threshold *)
  tcb_dupacks : N;        (* duplicate ACK counter *)
  tcb_recover : SeqNum;   (* recovery point for NewReno *)

  (* RTT estimation and RTO calculation (RFC 6298) *)
  tcb_srtt : N;           (* smoothed RTT *)
  tcb_rttvar : N;         (* RTT variance *)
  tcb_rto : N;            (* retransmission timeout *)
  tcb_backoff : N;        (* exponential backoff multiplier *)

  (* Timers *)
  tcb_retransmit_timer : option N;
  tcb_persist_timer    : option N;
  tcb_keepalive_timer  : option N;
  tcb_time_wait_timer  : option N;
  tcb_delack_timer     : option N;

  (* Options and negotiation *)
  tcb_mss : word16;
  tcb_window_scale : N;
  tcb_sack_permitted : bool;
  tcb_timestamps : bool;

  (* Bookkeeping *)
  tcb_last_ack_sent : SeqNum;
  tcb_fin_sent : bool;
  tcb_fin_rcvd : bool
}.

(* =============================================================================
   Section 7: TCP Options (RFC 9293 Section 3.2)
   ============================================================================= *)

Inductive TCPOption :=
  | OptEnd
  | OptNop
  | OptMSS (mss: word16)
  | OptWindowScale (scale: byte)
  | OptSACKPermitted
  | OptSACK (blocks: list (SeqNum * SeqNum))
  | OptTimestamp (val: word32) (echo: word32)
  | OptUnknown (kind: byte) (data: list byte).

Fixpoint bytes_to_words16 (bs : list byte) : list word16 :=
  match bs with
  | [] => []
  | b :: [] => [b * 256]
  | b1 :: b2 :: rest => (b1 * 256 + b2) :: bytes_to_words16 rest
  end.

Fixpoint parse_tcp_options_aux (opts : list byte) (fuel : nat) : list TCPOption :=
  match fuel with
  | O => []
  | S fuel' =>
      match opts with
      | [] => []
      | 0 :: _ => [OptEnd]
      | 1 :: rest => OptNop :: parse_tcp_options_aux rest fuel'
      | 2 :: 4 :: b1 :: b2 :: rest => OptMSS (b1 * 256 + b2) :: parse_tcp_options_aux rest fuel'
      | 3 :: 3 :: s :: rest => OptWindowScale s :: parse_tcp_options_aux rest fuel'
      | 4 :: 2 :: rest => OptSACKPermitted :: parse_tcp_options_aux rest fuel'
      | 8 :: 10 :: t1 :: t2 :: t3 :: t4 :: e1 :: e2 :: e3 :: e4 :: rest =>
          let ts := (((((t1 * 256) + t2) * 256) + t3) * 256) + t4 in
          let te := (((((e1 * 256) + e2) * 256) + e3) * 256) + e4 in
          OptTimestamp ts te :: parse_tcp_options_aux rest fuel'
      | k :: len :: rest =>
          if N.ltb len 2 then []
          else let n := (N.to_nat len - 2)%nat in
               let data := firstn n rest in
               let rem := skipn n rest in
               OptUnknown k data :: parse_tcp_options_aux rem fuel'
      | _ :: [] => []
      end
  end.

Definition parse_tcp_options (opts : list byte) : list TCPOption :=
  parse_tcp_options_aux opts (length opts).

(* =============================================================================
   Section 8: Checksum Calculation
   ============================================================================= *)

Record TCPPseudoHeader := {
  pseudo_src : word32;
  pseudo_dst : word32;
  pseudo_zero : byte;
  pseudo_protocol : byte;
  pseudo_tcp_length : word16
}.

Definition u32_bytes (x : word32) : list byte :=
  [ (x / 16777216) mod 256; (x / 65536) mod 256; (x / 256) mod 256; x mod 256 ].

Definition header_bytes_wo_checksum (hdr : TCPHeader) : list byte :=
  [ hdr.(tcp_src_port) / 256; hdr.(tcp_src_port) mod 256;
    hdr.(tcp_dst_port) / 256; hdr.(tcp_dst_port) mod 256 ] ++
  u32_bytes hdr.(tcp_seq) ++ u32_bytes hdr.(tcp_ack) ++
  [ (hdr.(tcp_data_offset) * 16 + hdr.(tcp_reserved) * 2 + (hdr.(tcp_flags) / 256)) mod 256;
    hdr.(tcp_flags) mod 256;
    hdr.(tcp_window) / 256; hdr.(tcp_window) mod 256;
    0; 0;
    hdr.(tcp_urgent) / 256; hdr.(tcp_urgent) mod 256 ] ++ hdr.(tcp_options).

Fixpoint ones_complement_fold (acc : N) (words : list word16) : N :=
  match words with
  | [] => acc
  | w :: rest =>
      let sum := acc + w in
      let carry := sum / 65536 in
      let low := sum mod 65536 in
      ones_complement_fold (carry + low) rest
  end.

Definition ones_complement (words : list word16) : word16 :=
  let s := ones_complement_fold 0 words in
  N.lxor (s mod 65536) (N.ones 16).

Definition pseudo_header_bytes (p : TCPPseudoHeader) : list byte :=
  u32_bytes p.(pseudo_src) ++ u32_bytes p.(pseudo_dst) ++
  [ p.(pseudo_zero); p.(pseudo_protocol) ] ++ [ p.(pseudo_tcp_length) / 256; p.(pseudo_tcp_length) mod 256 ].

Definition calculate_tcp_checksum (p : TCPPseudoHeader) (hdr : TCPHeader) (payload : list byte) : word16 :=
  let ws := bytes_to_words16 (pseudo_header_bytes p ++ header_bytes_wo_checksum hdr ++ payload) in
  ones_complement ws.

(* =============================================================================
   Section 9: Congestion Control (RFC 5681 - MUST-19)
   ============================================================================= *)

Definition is_in_slow_start (tcb : TCB) : bool := N.ltb tcb.(tcb_cwnd) tcb.(tcb_ssthresh).

Definition slow_start_increase (tcb : TCB) (acked_bytes : N) : TCB :=
  {| tcb_local_addr := tcb.(tcb_local_addr);
     tcb_remote_addr := tcb.(tcb_remote_addr);
     tcb_local_port := tcb.(tcb_local_port);
     tcb_remote_port := tcb.(tcb_remote_port);
     tcb_state := tcb.(tcb_state);
     tcb_snd_una := tcb.(tcb_snd_una);
     tcb_snd_nxt := tcb.(tcb_snd_nxt);
     tcb_snd_wnd := tcb.(tcb_snd_wnd);
     tcb_snd_up := tcb.(tcb_snd_up);
     tcb_snd_wl1 := tcb.(tcb_snd_wl1);
     tcb_snd_wl2 := tcb.(tcb_snd_wl2);
     tcb_iss := tcb.(tcb_iss);
     tcb_rcv_nxt := tcb.(tcb_rcv_nxt);
     tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
     tcb_rcv_up := tcb.(tcb_rcv_up);
     tcb_irs := tcb.(tcb_irs);
     tcb_rcv_queue := tcb.(tcb_rcv_queue);
     tcb_retrans_queue := tcb.(tcb_retrans_queue);
     tcb_cwnd := N.min (tcb.(tcb_cwnd) + acked_bytes) tcb.(tcb_ssthresh);
     tcb_ssthresh := tcb.(tcb_ssthresh);
     tcb_dupacks := 0;
     tcb_recover := tcb.(tcb_recover);
     tcb_srtt := tcb.(tcb_srtt);
     tcb_rttvar := tcb.(tcb_rttvar);
     tcb_rto := tcb.(tcb_rto);
     tcb_backoff := tcb.(tcb_backoff);
     tcb_retransmit_timer := tcb.(tcb_retransmit_timer);
     tcb_persist_timer := tcb.(tcb_persist_timer);
     tcb_keepalive_timer := tcb.(tcb_keepalive_timer);
     tcb_time_wait_timer := tcb.(tcb_time_wait_timer);
     tcb_delack_timer := tcb.(tcb_delack_timer);
     tcb_mss := tcb.(tcb_mss);
     tcb_window_scale := tcb.(tcb_window_scale);
     tcb_sack_permitted := tcb.(tcb_sack_permitted);
     tcb_timestamps := tcb.(tcb_timestamps);
     tcb_last_ack_sent := tcb.(tcb_last_ack_sent);
     tcb_fin_sent := tcb.(tcb_fin_sent);
     tcb_fin_rcvd := tcb.(tcb_fin_rcvd) |}.

Definition congestion_avoidance_increase (tcb : TCB) (acked_bytes : N) : TCB :=
  let inc := (tcb.(tcb_mss) * tcb.(tcb_mss)) / tcb.(tcb_cwnd) in
  {| tcb_local_addr := tcb.(tcb_local_addr);
     tcb_remote_addr := tcb.(tcb_remote_addr);
     tcb_local_port := tcb.(tcb_local_port);
     tcb_remote_port := tcb.(tcb_remote_port);
     tcb_state := tcb.(tcb_state);
     tcb_snd_una := tcb.(tcb_snd_una);
     tcb_snd_nxt := tcb.(tcb_snd_nxt);
     tcb_snd_wnd := tcb.(tcb_snd_wnd);
     tcb_snd_up := tcb.(tcb_snd_up);
     tcb_snd_wl1 := tcb.(tcb_snd_wl1);
     tcb_snd_wl2 := tcb.(tcb_snd_wl2);
     tcb_iss := tcb.(tcb_iss);
     tcb_rcv_nxt := tcb.(tcb_rcv_nxt);
     tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
     tcb_rcv_up := tcb.(tcb_rcv_up);
     tcb_irs := tcb.(tcb_irs);
     tcb_rcv_queue := tcb.(tcb_rcv_queue);
     tcb_retrans_queue := tcb.(tcb_retrans_queue);
     tcb_cwnd := tcb.(tcb_cwnd) + inc;
     tcb_ssthresh := tcb.(tcb_ssthresh);
     tcb_dupacks := 0;
     tcb_recover := tcb.(tcb_recover);
     tcb_srtt := tcb.(tcb_srtt);
     tcb_rttvar := tcb.(tcb_rttvar);
     tcb_rto := tcb.(tcb_rto);
     tcb_backoff := tcb.(tcb_backoff);
     tcb_retransmit_timer := tcb.(tcb_retransmit_timer);
     tcb_persist_timer := tcb.(tcb_persist_timer);
     tcb_keepalive_timer := tcb.(tcb_keepalive_timer);
     tcb_time_wait_timer := tcb.(tcb_time_wait_timer);
     tcb_delack_timer := tcb.(tcb_delack_timer);
     tcb_mss := tcb.(tcb_mss);
     tcb_window_scale := tcb.(tcb_window_scale);
     tcb_sack_permitted := tcb.(tcb_sack_permitted);
     tcb_timestamps := tcb.(tcb_timestamps);
     tcb_last_ack_sent := tcb.(tcb_last_ack_sent);
     tcb_fin_sent := tcb.(tcb_fin_sent);
     tcb_fin_rcvd := tcb.(tcb_fin_rcvd) |}.

Definition enter_loss_recovery (tcb : TCB) : TCB :=
  let new_ssthresh := N.max (tcb.(tcb_cwnd) / 2) MIN_CWND in
  {| tcb_local_addr := tcb.(tcb_local_addr);
     tcb_remote_addr := tcb.(tcb_remote_addr);
     tcb_local_port := tcb.(tcb_local_port);
     tcb_remote_port := tcb.(tcb_remote_port);
     tcb_state := tcb.(tcb_state);
     tcb_snd_una := tcb.(tcb_snd_una);
     tcb_snd_nxt := tcb.(tcb_snd_nxt);
     tcb_snd_wnd := tcb.(tcb_snd_wnd);
     tcb_snd_up := tcb.(tcb_snd_up);
     tcb_snd_wl1 := tcb.(tcb_snd_wl1);
     tcb_snd_wl2 := tcb.(tcb_snd_wl2);
     tcb_iss := tcb.(tcb_iss);
     tcb_rcv_nxt := tcb.(tcb_rcv_nxt);
     tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
     tcb_rcv_up := tcb.(tcb_rcv_up);
     tcb_irs := tcb.(tcb_irs);
     tcb_rcv_queue := tcb.(tcb_rcv_queue);
     tcb_retrans_queue := tcb.(tcb_retrans_queue);
     tcb_cwnd := new_ssthresh + 3 * tcb.(tcb_mss);
     tcb_ssthresh := new_ssthresh;
     tcb_dupacks := tcb.(tcb_dupacks);
     tcb_recover := tcb.(tcb_snd_nxt);
     tcb_srtt := tcb.(tcb_srtt);
     tcb_rttvar := tcb.(tcb_rttvar);
     tcb_rto := tcb.(tcb_rto);
     tcb_backoff := tcb.(tcb_backoff);
     tcb_retransmit_timer := tcb.(tcb_retransmit_timer);
     tcb_persist_timer := tcb.(tcb_persist_timer);
     tcb_keepalive_timer := tcb.(tcb_keepalive_timer);
     tcb_time_wait_timer := tcb.(tcb_time_wait_timer);
     tcb_delack_timer := tcb.(tcb_delack_timer);
     tcb_mss := tcb.(tcb_mss);
     tcb_window_scale := tcb.(tcb_window_scale);
     tcb_sack_permitted := tcb.(tcb_sack_permitted);
     tcb_timestamps := tcb.(tcb_timestamps);
     tcb_last_ack_sent := tcb.(tcb_last_ack_sent);
     tcb_fin_sent := tcb.(tcb_fin_sent);
     tcb_fin_rcvd := tcb.(tcb_fin_rcvd) |}.

(* RTO Exponential Backoff (RFC 6298 - part of MUST-19) *)
Definition exponential_backoff_rto (tcb : TCB) : TCB :=
  let new_backoff := tcb.(tcb_backoff) * 2 in
  let new_rto := N.min (tcb.(tcb_rto) * new_backoff) MAX_RTO in
  {| tcb_local_addr := tcb.(tcb_local_addr);
     tcb_remote_addr := tcb.(tcb_remote_addr);
     tcb_local_port := tcb.(tcb_local_port);
     tcb_remote_port := tcb.(tcb_remote_port);
     tcb_state := tcb.(tcb_state);
     tcb_snd_una := tcb.(tcb_snd_una);
     tcb_snd_nxt := tcb.(tcb_snd_nxt);
     tcb_snd_wnd := tcb.(tcb_snd_wnd);
     tcb_snd_up := tcb.(tcb_snd_up);
     tcb_snd_wl1 := tcb.(tcb_snd_wl1);
     tcb_snd_wl2 := tcb.(tcb_snd_wl2);
     tcb_iss := tcb.(tcb_iss);
     tcb_rcv_nxt := tcb.(tcb_rcv_nxt);
     tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
     tcb_rcv_up := tcb.(tcb_rcv_up);
     tcb_irs := tcb.(tcb_irs);
     tcb_rcv_queue := tcb.(tcb_rcv_queue);
     tcb_retrans_queue := tcb.(tcb_retrans_queue);
     tcb_cwnd := tcb.(tcb_cwnd);
     tcb_ssthresh := tcb.(tcb_ssthresh);
     tcb_dupacks := tcb.(tcb_dupacks);
     tcb_recover := tcb.(tcb_recover);
     tcb_srtt := tcb.(tcb_srtt);
     tcb_rttvar := tcb.(tcb_rttvar);
     tcb_rto := new_rto;
     tcb_backoff := new_backoff;
     tcb_retransmit_timer := Some new_rto;
     tcb_persist_timer := tcb.(tcb_persist_timer);
     tcb_keepalive_timer := tcb.(tcb_keepalive_timer);
     tcb_time_wait_timer := tcb.(tcb_time_wait_timer);
     tcb_delack_timer := tcb.(tcb_delack_timer);
     tcb_mss := tcb.(tcb_mss);
     tcb_window_scale := tcb.(tcb_window_scale);
     tcb_sack_permitted := tcb.(tcb_sack_permitted);
     tcb_timestamps := tcb.(tcb_timestamps);
     tcb_last_ack_sent := tcb.(tcb_last_ack_sent);
     tcb_fin_sent := tcb.(tcb_fin_sent);
     tcb_fin_rcvd := tcb.(tcb_fin_rcvd) |}.

(* =============================================================================
   Section 10: Retransmission Management
   ============================================================================= *)

Definition add_to_retrans_queue (tcb : TCB) (seq : SeqNum) (data : list byte) (timestamp : N) : TCB :=
  let entry := {| re_seq := seq;
                  re_len := N.of_nat (length data);
                  re_data := data;
                  re_timestamp := timestamp;
                  re_retrans_count := 0 |} in
  {| tcb_local_addr := tcb.(tcb_local_addr);
     tcb_remote_addr := tcb.(tcb_remote_addr);
     tcb_local_port := tcb.(tcb_local_port);
     tcb_remote_port := tcb.(tcb_remote_port);
     tcb_state := tcb.(tcb_state);
     tcb_snd_una := tcb.(tcb_snd_una);
     tcb_snd_nxt := tcb.(tcb_snd_nxt);
     tcb_snd_wnd := tcb.(tcb_snd_wnd);
     tcb_snd_up := tcb.(tcb_snd_up);
     tcb_snd_wl1 := tcb.(tcb_snd_wl1);
     tcb_snd_wl2 := tcb.(tcb_snd_wl2);
     tcb_iss := tcb.(tcb_iss);
     tcb_rcv_nxt := tcb.(tcb_rcv_nxt);
     tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
     tcb_rcv_up := tcb.(tcb_rcv_up);
     tcb_irs := tcb.(tcb_irs);
     tcb_rcv_queue := tcb.(tcb_rcv_queue);
     tcb_retrans_queue := tcb.(tcb_retrans_queue) ++ [entry];
     tcb_cwnd := tcb.(tcb_cwnd);
     tcb_ssthresh := tcb.(tcb_ssthresh);
     tcb_dupacks := tcb.(tcb_dupacks);
     tcb_recover := tcb.(tcb_recover);
     tcb_srtt := tcb.(tcb_srtt);
     tcb_rttvar := tcb.(tcb_rttvar);
     tcb_rto := tcb.(tcb_rto);
     tcb_backoff := tcb.(tcb_backoff);
     tcb_retransmit_timer := Some tcb.(tcb_rto);
     tcb_persist_timer := tcb.(tcb_persist_timer);
     tcb_keepalive_timer := tcb.(tcb_keepalive_timer);
     tcb_time_wait_timer := tcb.(tcb_time_wait_timer);
     tcb_delack_timer := tcb.(tcb_delack_timer);
     tcb_mss := tcb.(tcb_mss);
     tcb_window_scale := tcb.(tcb_window_scale);
     tcb_sack_permitted := tcb.(tcb_sack_permitted);
     tcb_timestamps := tcb.(tcb_timestamps);
     tcb_last_ack_sent := tcb.(tcb_last_ack_sent);
     tcb_fin_sent := tcb.(tcb_fin_sent);
     tcb_fin_rcvd := tcb.(tcb_fin_rcvd) |}.

Fixpoint remove_acked_from_queue (queue : list RetransmitEntry) (ack_num : AckNum) : list RetransmitEntry :=
  match queue with
  | [] => []
  | entry :: rest =>
      if seq_lt (seq_add entry.(re_seq) entry.(re_len)) ack_num
      then remove_acked_from_queue rest ack_num
      else entry :: remove_acked_from_queue rest ack_num
  end.

(* =============================================================================
   Section 11: Segment Processing Primitives (RFC 9293 Section 3.10)
   ============================================================================= *)

Definition segment_length (hdr : TCPHeader) (data_len : N) : N :=
  let syn := if is_syn_segment hdr then 1 else 0 in
  let fin := if is_fin_segment hdr then 1 else 0 in
  data_len + syn + fin.

Definition segment_acceptable (tcb : TCB) (seg_seq : SeqNum) (seg_len : N) : bool :=
  let rcv_nxt := tcb.(tcb_rcv_nxt) in
  let rcv_wnd := tcb.(tcb_rcv_wnd) in
  if N.eqb seg_len 0 then
    if N.eqb rcv_wnd 0 then N.eqb seg_seq rcv_nxt
    else andb (seq_leq rcv_nxt seg_seq) (seq_lt seg_seq (seq_add rcv_nxt rcv_wnd))
  else if N.eqb rcv_wnd 0 then false else
    orb (andb (seq_leq rcv_nxt seg_seq) (seq_lt seg_seq (seq_add rcv_nxt rcv_wnd)))
        (andb (seq_leq rcv_nxt (seq_add seg_seq (seg_len - 1)))
              (seq_lt (seq_add seg_seq (seg_len - 1)) (seq_add rcv_nxt rcv_wnd))).

Definition ack_acceptable (tcb : TCB) (seg_ack : AckNum) : bool :=
  andb (seq_lt tcb.(tcb_snd_una) seg_ack) (seq_leq seg_ack tcb.(tcb_snd_nxt)).

Definition update_window (tcb : TCB) (seg_seq : SeqNum) (seg_ack : AckNum) (seg_wnd : word16) : TCB :=
  if orb (seq_lt tcb.(tcb_snd_wl1) seg_seq)
         (andb (N.eqb tcb.(tcb_snd_wl1) seg_seq) (seq_leq tcb.(tcb_snd_wl2) seg_ack)) then
    {| tcb_local_addr := tcb.(tcb_local_addr);
       tcb_remote_addr := tcb.(tcb_remote_addr);
       tcb_local_port := tcb.(tcb_local_port);
       tcb_remote_port := tcb.(tcb_remote_port);
       tcb_state := tcb.(tcb_state);
       tcb_snd_una := tcb.(tcb_snd_una);
       tcb_snd_nxt := tcb.(tcb_snd_nxt);
       tcb_snd_wnd := seg_wnd;
       tcb_snd_up := tcb.(tcb_snd_up);
       tcb_snd_wl1 := seg_seq;
       tcb_snd_wl2 := seg_ack;
       tcb_iss := tcb.(tcb_iss);
       tcb_rcv_nxt := tcb.(tcb_rcv_nxt);
       tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
       tcb_rcv_up := tcb.(tcb_rcv_up);
       tcb_irs := tcb.(tcb_irs);
       tcb_rcv_queue := tcb.(tcb_rcv_queue);
       tcb_retrans_queue := tcb.(tcb_retrans_queue);
       tcb_cwnd := tcb.(tcb_cwnd);
       tcb_ssthresh := tcb.(tcb_ssthresh);
       tcb_dupacks := tcb.(tcb_dupacks);
       tcb_recover := tcb.(tcb_recover);
       tcb_srtt := tcb.(tcb_srtt);
       tcb_rttvar := tcb.(tcb_rttvar);
       tcb_rto := tcb.(tcb_rto);
       tcb_backoff := tcb.(tcb_backoff);
       tcb_retransmit_timer := tcb.(tcb_retransmit_timer);
       tcb_persist_timer := tcb.(tcb_persist_timer);
       tcb_keepalive_timer := tcb.(tcb_keepalive_timer);
       tcb_time_wait_timer := tcb.(tcb_time_wait_timer);
       tcb_delack_timer := tcb.(tcb_delack_timer);
       tcb_mss := tcb.(tcb_mss);
       tcb_window_scale := tcb.(tcb_window_scale);
       tcb_sack_permitted := tcb.(tcb_sack_permitted);
       tcb_timestamps := tcb.(tcb_timestamps);
       tcb_last_ack_sent := tcb.(tcb_last_ack_sent);
       tcb_fin_sent := tcb.(tcb_fin_sent);
       tcb_fin_rcvd := tcb.(tcb_fin_rcvd) |}
  else tcb.

Definition generate_ack (tcb : TCB) : TCPHeader :=
  {| tcp_src_port := tcb.(tcb_local_port);
     tcp_dst_port := tcb.(tcb_remote_port);
     tcp_seq := tcb.(tcb_snd_nxt);
     tcp_ack := tcb.(tcb_rcv_nxt);
     tcp_data_offset := 5;
     tcp_reserved := 0;
     tcp_flags := set_flag 0 FLAG_ACK;
     tcp_window := tcb.(tcb_rcv_wnd);
     tcp_checksum := 0;
     tcp_urgent := 0;
     tcp_options := [] |}.

Definition generate_rst (tcb : TCB) (seg : TCPHeader) (payload_len : N) : TCPHeader :=
  if is_ack_segment seg then
    {| tcp_src_port := tcb.(tcb_local_port);
       tcp_dst_port := tcb.(tcb_remote_port);
       tcp_seq := seg.(tcp_ack);
       tcp_ack := 0;
       tcp_data_offset := 5; tcp_reserved := 0;
       tcp_flags := set_flag 0 FLAG_RST;
       tcp_window := 0; tcp_checksum := 0; tcp_urgent := 0; tcp_options := [] |}
  else
    let slen := segment_length seg payload_len in
    {| tcp_src_port := tcb.(tcb_local_port);
       tcp_dst_port := tcb.(tcb_remote_port);
       tcp_seq := 0;
       tcp_ack := seq_add seg.(tcp_seq) slen;
       tcp_data_offset := 5; tcp_reserved := 0;
       tcp_flags := set_flag (set_flag 0 FLAG_RST) FLAG_ACK;
       tcp_window := 0; tcp_checksum := 0; tcp_urgent := 0; tcp_options := [] |}.

(* =============================================================================
   Section 12: Receive Reassembly Helpers
   ============================================================================= *)

Definition mk_range (s : SeqNum) (len : N) : ReassemblyRange := {| rr_start := s; rr_len := len |}.

Definition offset_from_rcv (base : SeqNum) (s : SeqNum) : N := (s - base) mod SEQ_MOD.

Fixpoint insert_sorted (base : SeqNum) (newr : ReassemblyRange) (q : list ReassemblyRange) : list ReassemblyRange :=
  match q with
  | [] => [newr]
  | r :: rs =>
      let off_n := offset_from_rcv base newr.(rr_start) in
      let off_r := offset_from_rcv base r.(rr_start) in
      if N.leb off_n off_r then newr :: q else r :: insert_sorted base newr rs
  end.

Fixpoint coalesce_from (base : SeqNum) (acc : ReassemblyRange) (q : list ReassemblyRange) : list ReassemblyRange :=
  match q with
  | [] => [acc]
  | r :: rs =>
      let off_acc := offset_from_rcv base acc.(rr_start) in
      let end_acc := off_acc + acc.(rr_len) in
      let off_r := offset_from_rcv base r.(rr_start) in
      if N.leb off_r end_acc then
        let end_r := off_r + r.(rr_len) in
        let new_end := if N.leb end_acc end_r then end_r else end_acc in
        let new_len := new_end - off_acc in
        let acc' := mk_range acc.(rr_start) new_len in
        coalesce_from base acc' rs
      else acc :: coalesce_from base r rs
  end.

Definition coalesce_sorted (base : SeqNum) (q : list ReassemblyRange) : list ReassemblyRange :=
  match q with
  | [] => []
  | r :: rs => coalesce_from base r rs
  end.

Fixpoint advance_contiguous (fuel : nat) (base : SeqNum) (q : list ReassemblyRange) : SeqNum * list ReassemblyRange :=
  match fuel with
  | O => (base, q)
  | S fuel' =>
      match q with
      | [] => (base, [])
      | r :: rs =>
          if N.eqb (offset_from_rcv base r.(rr_start)) 0 then
            let base' := seq_add base r.(rr_len) in
            advance_contiguous fuel' base' rs
          else (base, q)
      end
  end.

Definition reassembly_update (tcb : TCB) (seg_seq : SeqNum) (seg_len : N) : TCB :=
  if N.eqb seg_len 0 then tcb else
  let q1 := insert_sorted tcb.(tcb_rcv_nxt) (mk_range seg_seq seg_len) tcb.(tcb_rcv_queue) in
  let q2 := coalesce_sorted tcb.(tcb_rcv_nxt) q1 in
  let '(new_rcv_nxt, q3) := advance_contiguous (length q2) tcb.(tcb_rcv_nxt) q2 in
  {| tcb_local_addr := tcb.(tcb_local_addr);
     tcb_remote_addr := tcb.(tcb_remote_addr);
     tcb_local_port := tcb.(tcb_local_port);
     tcb_remote_port := tcb.(tcb_remote_port);
     tcb_state := tcb.(tcb_state);
     tcb_snd_una := tcb.(tcb_snd_una); tcb_snd_nxt := tcb.(tcb_snd_nxt); tcb_snd_wnd := tcb.(tcb_snd_wnd);
     tcb_snd_up := tcb.(tcb_snd_up); tcb_snd_wl1 := tcb.(tcb_snd_wl1); tcb_snd_wl2 := tcb.(tcb_snd_wl2); tcb_iss := tcb.(tcb_iss);
     tcb_rcv_nxt := new_rcv_nxt; tcb_rcv_wnd := tcb.(tcb_rcv_wnd); tcb_rcv_up := tcb.(tcb_rcv_up); tcb_irs := tcb.(tcb_irs);
     tcb_rcv_queue := q3;
     tcb_retrans_queue := tcb.(tcb_retrans_queue);
     tcb_cwnd := tcb.(tcb_cwnd); tcb_ssthresh := tcb.(tcb_ssthresh); tcb_dupacks := tcb.(tcb_dupacks); tcb_recover := tcb.(tcb_recover);
     tcb_srtt := tcb.(tcb_srtt); tcb_rttvar := tcb.(tcb_rttvar); tcb_rto := tcb.(tcb_rto); tcb_backoff := tcb.(tcb_backoff);
     tcb_retransmit_timer := tcb.(tcb_retransmit_timer); tcb_persist_timer := tcb.(tcb_persist_timer);
     tcb_keepalive_timer := tcb.(tcb_keepalive_timer); tcb_time_wait_timer := tcb.(tcb_time_wait_timer); tcb_delack_timer := tcb.(tcb_delack_timer);
     tcb_mss := tcb.(tcb_mss); tcb_window_scale := tcb.(tcb_window_scale); tcb_sack_permitted := tcb.(tcb_sack_permitted); tcb_timestamps := tcb.(tcb_timestamps);
     tcb_last_ack_sent := tcb.(tcb_last_ack_sent); tcb_fin_sent := tcb.(tcb_fin_sent); tcb_fin_rcvd := tcb.(tcb_fin_rcvd) |}.

(* =============================================================================
   Section 13: Complete TCP State Machine (RFC 9293 Section 3.10)
   ============================================================================= *)

Definition process_ack_in_established (tcb : TCB) (seg_ack : AckNum) : TCB :=
  if ack_acceptable tcb seg_ack then
    let acked_bytes := (seg_ack - tcb.(tcb_snd_una)) mod SEQ_MOD in
    let new_retrans_queue := remove_acked_from_queue tcb.(tcb_retrans_queue) seg_ack in
    let tcb1 := {| tcb_local_addr := tcb.(tcb_local_addr);
                   tcb_remote_addr := tcb.(tcb_remote_addr);
                   tcb_local_port := tcb.(tcb_local_port);
                   tcb_remote_port := tcb.(tcb_remote_port);
                   tcb_state := tcb.(tcb_state);
                   tcb_snd_una := seg_ack;
                   tcb_snd_nxt := tcb.(tcb_snd_nxt);
                   tcb_snd_wnd := tcb.(tcb_snd_wnd);
                   tcb_snd_up := tcb.(tcb_snd_up);
                   tcb_snd_wl1 := tcb.(tcb_snd_wl1);
                   tcb_snd_wl2 := tcb.(tcb_snd_wl2);
                   tcb_iss := tcb.(tcb_iss);
                   tcb_rcv_nxt := tcb.(tcb_rcv_nxt);
                   tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
                   tcb_rcv_up := tcb.(tcb_rcv_up);
                   tcb_irs := tcb.(tcb_irs);
                   tcb_rcv_queue := tcb.(tcb_rcv_queue);
                   tcb_retrans_queue := new_retrans_queue;
                   tcb_cwnd := tcb.(tcb_cwnd);
                   tcb_ssthresh := tcb.(tcb_ssthresh);
                   tcb_dupacks := tcb.(tcb_dupacks);
                   tcb_recover := tcb.(tcb_recover);
                   tcb_srtt := tcb.(tcb_srtt);
                   tcb_rttvar := tcb.(tcb_rttvar);
                   tcb_rto := tcb.(tcb_rto);
                   tcb_backoff := 1;
                   tcb_retransmit_timer := if N.eqb (N.of_nat (length new_retrans_queue)) 0 then None else Some tcb.(tcb_rto);
                   tcb_persist_timer := tcb.(tcb_persist_timer);
                   tcb_keepalive_timer := tcb.(tcb_keepalive_timer);
                   tcb_time_wait_timer := tcb.(tcb_time_wait_timer);
                   tcb_delack_timer := tcb.(tcb_delack_timer);
                   tcb_mss := tcb.(tcb_mss);
                   tcb_window_scale := tcb.(tcb_window_scale);
                   tcb_sack_permitted := tcb.(tcb_sack_permitted);
                   tcb_timestamps := tcb.(tcb_timestamps);
                   tcb_last_ack_sent := tcb.(tcb_last_ack_sent);
                   tcb_fin_sent := tcb.(tcb_fin_sent);
                   tcb_fin_rcvd := tcb.(tcb_fin_rcvd) |} in
    (* Apply congestion control *)
    if is_in_slow_start tcb1 then
      slow_start_increase tcb1 acked_bytes
    else
      congestion_avoidance_increase tcb1 acked_bytes
  else if N.eqb seg_ack tcb.(tcb_snd_una) then
    (* Duplicate ACK *)
    let tcb1 := {| tcb_local_addr := tcb.(tcb_local_addr);
                   tcb_remote_addr := tcb.(tcb_remote_addr);
                   tcb_local_port := tcb.(tcb_local_port);
                   tcb_remote_port := tcb.(tcb_remote_port);
                   tcb_state := tcb.(tcb_state);
                   tcb_snd_una := tcb.(tcb_snd_una);
                   tcb_snd_nxt := tcb.(tcb_snd_nxt);
                   tcb_snd_wnd := tcb.(tcb_snd_wnd);
                   tcb_snd_up := tcb.(tcb_snd_up);
                   tcb_snd_wl1 := tcb.(tcb_snd_wl1);
                   tcb_snd_wl2 := tcb.(tcb_snd_wl2);
                   tcb_iss := tcb.(tcb_iss);
                   tcb_rcv_nxt := tcb.(tcb_rcv_nxt);
                   tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
                   tcb_rcv_up := tcb.(tcb_rcv_up);
                   tcb_irs := tcb.(tcb_irs);
                   tcb_rcv_queue := tcb.(tcb_rcv_queue);
                   tcb_retrans_queue := tcb.(tcb_retrans_queue);
                   tcb_cwnd := tcb.(tcb_cwnd);
                   tcb_ssthresh := tcb.(tcb_ssthresh);
                   tcb_dupacks := tcb.(tcb_dupacks) + 1;
                   tcb_recover := tcb.(tcb_recover);
                   tcb_srtt := tcb.(tcb_srtt);
                   tcb_rttvar := tcb.(tcb_rttvar);
                   tcb_rto := tcb.(tcb_rto);
                   tcb_backoff := tcb.(tcb_backoff);
                   tcb_retransmit_timer := tcb.(tcb_retransmit_timer);
                   tcb_persist_timer := tcb.(tcb_persist_timer);
                   tcb_keepalive_timer := tcb.(tcb_keepalive_timer);
                   tcb_time_wait_timer := tcb.(tcb_time_wait_timer);
                   tcb_delack_timer := tcb.(tcb_delack_timer);
                   tcb_mss := tcb.(tcb_mss);
                   tcb_window_scale := tcb.(tcb_window_scale);
                   tcb_sack_permitted := tcb.(tcb_sack_permitted);
                   tcb_timestamps := tcb.(tcb_timestamps);
                   tcb_last_ack_sent := tcb.(tcb_last_ack_sent);
                   tcb_fin_sent := tcb.(tcb_fin_sent);
                   tcb_fin_rcvd := tcb.(tcb_fin_rcvd) |} in
    if N.eqb tcb1.(tcb_dupacks) 3 then enter_loss_recovery tcb1 else tcb1
  else tcb.

Definition tcp_process_segment
  (tcb : TCB) (seg : TCPHeader) (payload : list byte)
  : TCB * option TCPHeader * option (list byte) :=
  if negb (valid_header seg) then (tcb, Some (generate_rst tcb seg (N.of_nat (length payload))), None)
  else let seg_len := segment_length seg (N.of_nat (length payload)) in
       match tcb.(tcb_state) with
       | CLOSED => 
           (tcb, Some (generate_rst tcb seg (N.of_nat (length payload))), None)
           
       | LISTEN =>
           if is_rst_segment seg then (tcb, None, None) else
           if is_ack_segment seg then (tcb, Some (generate_rst tcb seg (N.of_nat (length payload))), None) else
           if is_syn_segment seg then
             let iss := tcb.(tcb_iss) in
             let irs := seg.(tcp_seq) in
             let tcb' := {| tcb_local_addr := tcb.(tcb_local_addr);
                            tcb_remote_addr := tcb.(tcb_remote_addr);
                            tcb_local_port := tcb.(tcb_local_port);
                            tcb_remote_port := seg.(tcp_src_port);
                            tcb_state := SYN_RECEIVED;
                            tcb_snd_una := iss; tcb_snd_nxt := seq_add iss 1; tcb_snd_wnd := tcb.(tcb_snd_wnd);
                            tcb_snd_up := tcb.(tcb_snd_up); tcb_snd_wl1 := seg.(tcp_seq); tcb_snd_wl2 := seg.(tcp_seq);
                            tcb_iss := iss;
                            tcb_rcv_nxt := seq_add irs 1; tcb_rcv_wnd := tcb.(tcb_rcv_wnd); tcb_rcv_up := tcb.(tcb_rcv_up);
                            tcb_irs := irs; tcb_rcv_queue := tcb.(tcb_rcv_queue);
                            tcb_retrans_queue := [];
                            tcb_cwnd := INITIAL_CWND; tcb_ssthresh := INITIAL_SSTHRESH; tcb_dupacks := 0; tcb_recover := 0;
                            tcb_srtt := 0; tcb_rttvar := 0; tcb_rto := INITIAL_RTO; tcb_backoff := 1;
                            tcb_retransmit_timer := Some INITIAL_RTO; tcb_persist_timer := tcb.(tcb_persist_timer);
                            tcb_keepalive_timer := tcb.(tcb_keepalive_timer); tcb_time_wait_timer := None; tcb_delack_timer := None;
                            tcb_mss := tcb.(tcb_mss); tcb_window_scale := tcb.(tcb_window_scale);
                            tcb_sack_permitted := tcb.(tcb_sack_permitted); tcb_timestamps := tcb.(tcb_timestamps);
                            tcb_last_ack_sent := irs; tcb_fin_sent := false; tcb_fin_rcvd := false |} in
             let syn_ack := {| tcp_src_port := tcb'.(tcb_local_port);
                               tcp_dst_port := tcb'.(tcb_remote_port);
                               tcp_seq := iss; tcp_ack := tcb'.(tcb_rcv_nxt);
                               tcp_data_offset := 5; tcp_reserved := 0;
                               tcp_flags := set_flag (set_flag 0 FLAG_SYN) FLAG_ACK;
                               tcp_window := tcb'.(tcb_rcv_wnd); tcp_checksum := 0; tcp_urgent := 0; tcp_options := [] |} in
             (tcb', Some syn_ack, None)
           else (tcb, None, None)
           
       | SYN_SENT =>
           if is_ack_segment seg then
             if negb (ack_acceptable tcb seg.(tcp_ack)) then
               if is_rst_segment seg then (tcb, None, None)
               else (tcb, Some (generate_rst tcb seg (N.of_nat (length payload))), None)
             else if is_rst_segment seg then
               ({| tcb_local_addr := tcb.(tcb_local_addr);
                   tcb_remote_addr := tcb.(tcb_remote_addr);
                   tcb_local_port := tcb.(tcb_local_port);
                   tcb_remote_port := tcb.(tcb_remote_port);
                   tcb_state := CLOSED;
                   tcb_snd_una := tcb.(tcb_snd_una); tcb_snd_nxt := tcb.(tcb_snd_nxt); tcb_snd_wnd := tcb.(tcb_snd_wnd);
                   tcb_snd_up := tcb.(tcb_snd_up); tcb_snd_wl1 := tcb.(tcb_snd_wl1); tcb_snd_wl2 := tcb.(tcb_snd_wl2); tcb_iss := tcb.(tcb_iss);
                   tcb_rcv_nxt := tcb.(tcb_rcv_nxt); tcb_rcv_wnd := tcb.(tcb_rcv_wnd); tcb_rcv_up := tcb.(tcb_rcv_up); tcb_irs := tcb.(tcb_irs);
                   tcb_rcv_queue := tcb.(tcb_rcv_queue); tcb_retrans_queue := [];
                   tcb_cwnd := INITIAL_CWND; tcb_ssthresh := INITIAL_SSTHRESH; tcb_dupacks := 0; tcb_recover := 0;
                   tcb_srtt := 0; tcb_rttvar := 0; tcb_rto := INITIAL_RTO; tcb_backoff := 1;
                   tcb_retransmit_timer := None; tcb_persist_timer := None; tcb_keepalive_timer := None; 
                   tcb_time_wait_timer := None; tcb_delack_timer := None;
                   tcb_mss := tcb.(tcb_mss); tcb_window_scale := tcb.(tcb_window_scale); 
                   tcb_sack_permitted := tcb.(tcb_sack_permitted); tcb_timestamps := tcb.(tcb_timestamps);
                   tcb_last_ack_sent := tcb.(tcb_last_ack_sent); tcb_fin_sent := false; tcb_fin_rcvd := false |}, None, None)
             else if is_syn_segment seg then
               let tcb' := {| tcb_local_addr := tcb.(tcb_local_addr);
                              tcb_remote_addr := tcb.(tcb_remote_addr);
                              tcb_local_port := tcb.(tcb_local_port);
                              tcb_remote_port := tcb.(tcb_remote_port);
                              tcb_state := ESTABLISHED;
                              tcb_snd_una := seg.(tcp_ack); tcb_snd_nxt := seg.(tcp_ack); tcb_snd_wnd := seg.(tcp_window);
                              tcb_snd_up := tcb.(tcb_snd_up); tcb_snd_wl1 := seg.(tcp_seq); tcb_snd_wl2 := seg.(tcp_ack);
                              tcb_iss := tcb.(tcb_iss);
                              tcb_rcv_nxt := seq_add seg.(tcp_seq) 1; tcb_rcv_wnd := tcb.(tcb_rcv_wnd); 
                              tcb_rcv_up := tcb.(tcb_rcv_up);
                              tcb_irs := seg.(tcp_seq); tcb_rcv_queue := tcb.(tcb_rcv_queue);
                              tcb_retrans_queue := [];
                              tcb_cwnd := INITIAL_CWND; tcb_ssthresh := INITIAL_SSTHRESH; 
                              tcb_dupacks := 0; tcb_recover := 0;
                              tcb_srtt := 0; tcb_rttvar := 0; tcb_rto := INITIAL_RTO; tcb_backoff := 1;
                              tcb_retransmit_timer := None; tcb_persist_timer := None; tcb_keepalive_timer := None; 
                              tcb_time_wait_timer := None; tcb_delack_timer := None;
                              tcb_mss := tcb.(tcb_mss); tcb_window_scale := tcb.(tcb_window_scale); 
                              tcb_sack_permitted := tcb.(tcb_sack_permitted); tcb_timestamps := tcb.(tcb_timestamps);
                              tcb_last_ack_sent := seg.(tcp_seq); tcb_fin_sent := false; tcb_fin_rcvd := false |} in
               (tcb', Some (generate_ack tcb'), None)
             else (tcb, None, None)
           else (tcb, None, None)
           
       | SYN_RECEIVED =>
           if is_rst_segment seg then
             if segment_acceptable tcb seg.(tcp_seq) seg_len then
               ({| tcb_local_addr := tcb.(tcb_local_addr);
                   tcb_remote_addr := tcb.(tcb_remote_addr);
                   tcb_local_port := tcb.(tcb_local_port);
                   tcb_remote_port := tcb.(tcb_remote_port);
                   tcb_state := LISTEN;
                   tcb_snd_una := tcb.(tcb_snd_una); tcb_snd_nxt := tcb.(tcb_snd_nxt); tcb_snd_wnd := tcb.(tcb_snd_wnd);
                   tcb_snd_up := tcb.(tcb_snd_up); tcb_snd_wl1 := tcb.(tcb_snd_wl1); tcb_snd_wl2 := tcb.(tcb_snd_wl2); 
                   tcb_iss := tcb.(tcb_iss);
                   tcb_rcv_nxt := tcb.(tcb_rcv_nxt); tcb_rcv_wnd := tcb.(tcb_rcv_wnd); tcb_rcv_up := tcb.(tcb_rcv_up); 
                   tcb_irs := tcb.(tcb_irs);
                   tcb_rcv_queue := []; tcb_retrans_queue := [];
                   tcb_cwnd := INITIAL_CWND; tcb_ssthresh := INITIAL_SSTHRESH; tcb_dupacks := 0; tcb_recover := 0;
                   tcb_srtt := 0; tcb_rttvar := 0; tcb_rto := INITIAL_RTO; tcb_backoff := 1;
                   tcb_retransmit_timer := None; tcb_persist_timer := None; tcb_keepalive_timer := None; 
                   tcb_time_wait_timer := None; tcb_delack_timer := None;
                   tcb_mss := tcb.(tcb_mss); tcb_window_scale := tcb.(tcb_window_scale); 
                   tcb_sack_permitted := tcb.(tcb_sack_permitted); tcb_timestamps := tcb.(tcb_timestamps);
                   tcb_last_ack_sent := tcb.(tcb_last_ack_sent); tcb_fin_sent := false; tcb_fin_rcvd := false |}, None, None)
             else (tcb, None, None)
           else if is_ack_segment seg then
             if ack_acceptable tcb seg.(tcp_ack) then
               let tcb' := {| tcb_local_addr := tcb.(tcb_local_addr);
                              tcb_remote_addr := tcb.(tcb_remote_addr);
                              tcb_local_port := tcb.(tcb_local_port);
                              tcb_remote_port := tcb.(tcb_remote_port);
                              tcb_state := ESTABLISHED;
                              tcb_snd_una := seg.(tcp_ack); tcb_snd_nxt := tcb.(tcb_snd_nxt); 
                              tcb_snd_wnd := seg.(tcp_window);
                              tcb_snd_up := tcb.(tcb_snd_up); tcb_snd_wl1 := seg.(tcp_seq); 
                              tcb_snd_wl2 := seg.(tcp_ack);
                              tcb_iss := tcb.(tcb_iss);
                              tcb_rcv_nxt := tcb.(tcb_rcv_nxt); tcb_rcv_wnd := tcb.(tcb_rcv_wnd); 
                              tcb_rcv_up := tcb.(tcb_rcv_up);
                              tcb_irs := tcb.(tcb_irs); tcb_rcv_queue := tcb.(tcb_rcv_queue);
                              tcb_retrans_queue := tcb.(tcb_retrans_queue);
                              tcb_cwnd := tcb.(tcb_cwnd); tcb_ssthresh := tcb.(tcb_ssthresh); 
                              tcb_dupacks := 0; tcb_recover := tcb.(tcb_recover);
                              tcb_srtt := tcb.(tcb_srtt); tcb_rttvar := tcb.(tcb_rttvar); 
                              tcb_rto := tcb.(tcb_rto); tcb_backoff := 1;
                              tcb_retransmit_timer := None; tcb_persist_timer := None; 
                              tcb_keepalive_timer := None; 
                              tcb_time_wait_timer := None; tcb_delack_timer := None;
                              tcb_mss := tcb.(tcb_mss); tcb_window_scale := tcb.(tcb_window_scale); 
                              tcb_sack_permitted := tcb.(tcb_sack_permitted); 
                              tcb_timestamps := tcb.(tcb_timestamps);
                              tcb_last_ack_sent := tcb.(tcb_last_ack_sent); 
                              tcb_fin_sent := false; tcb_fin_rcvd := false |} in
               (tcb', None, Some payload)
             else (tcb, Some (generate_rst tcb seg (N.of_nat (length payload))), None)
           else (tcb, None, None)
           
       | ESTABLISHED =>
           if is_rst_segment seg then
             if segment_acceptable tcb seg.(tcp_seq) seg_len then
               ({| tcb_local_addr := tcb.(tcb_local_addr);
                   tcb_remote_addr := tcb.(tcb_remote_addr);
                   tcb_local_port := tcb.(tcb_local_port);
                   tcb_remote_port := tcb.(tcb_remote_port);
                   tcb_state := CLOSED;
                   tcb_snd_una := tcb.(tcb_snd_una); tcb_snd_nxt := tcb.(tcb_snd_nxt); tcb_snd_wnd := tcb.(tcb_snd_wnd);
                   tcb_snd_up := tcb.(tcb_snd_up); tcb_snd_wl1 := tcb.(tcb_snd_wl1); tcb_snd_wl2 := tcb.(tcb_snd_wl2); 
                   tcb_iss := tcb.(tcb_iss);
                   tcb_rcv_nxt := tcb.(tcb_rcv_nxt); tcb_rcv_wnd := tcb.(tcb_rcv_wnd); tcb_rcv_up := tcb.(tcb_rcv_up); 
                   tcb_irs := tcb.(tcb_irs);
                   tcb_rcv_queue := []; tcb_retrans_queue := [];
                   tcb_cwnd := INITIAL_CWND; tcb_ssthresh := INITIAL_SSTHRESH; tcb_dupacks := 0; tcb_recover := 0;
                   tcb_srtt := 0; tcb_rttvar := 0; tcb_rto := INITIAL_RTO; tcb_backoff := 1;
                   tcb_retransmit_timer := None; tcb_persist_timer := None; tcb_keepalive_timer := None; 
                   tcb_time_wait_timer := None; tcb_delack_timer := None;
                   tcb_mss := tcb.(tcb_mss); tcb_window_scale := tcb.(tcb_window_scale); 
                   tcb_sack_permitted := tcb.(tcb_sack_permitted); tcb_timestamps := tcb.(tcb_timestamps);
                   tcb_last_ack_sent := tcb.(tcb_last_ack_sent); tcb_fin_sent := false; tcb_fin_rcvd := false |}, None, None)
             else (tcb, None, None)
           else
             let tcb1 := if is_ack_segment seg then process_ack_in_established tcb seg.(tcp_ack) else tcb in
             let tcb2 := update_window tcb1 seg.(tcp_seq) seg.(tcp_ack) seg.(tcp_window) in
             let tcb3 := reassembly_update tcb2 seg.(tcp_seq) (N.of_nat (length payload)) in
             if is_fin_segment seg then
               let tcb4 := {| tcb_local_addr := tcb3.(tcb_local_addr);
                              tcb_remote_addr := tcb3.(tcb_remote_addr);
                              tcb_local_port := tcb3.(tcb_local_port);
                              tcb_remote_port := tcb3.(tcb_remote_port);
                              tcb_state := CLOSE_WAIT;
                              tcb_snd_una := tcb3.(tcb_snd_una); tcb_snd_nxt := tcb3.(tcb_snd_nxt); 
                              tcb_snd_wnd := tcb3.(tcb_snd_wnd);
                              tcb_snd_up := tcb3.(tcb_snd_up); tcb_snd_wl1 := tcb3.(tcb_snd_wl1); 
                              tcb_snd_wl2 := tcb3.(tcb_snd_wl2);
                              tcb_iss := tcb3.(tcb_iss);
                              tcb_rcv_nxt := seq_add tcb3.(tcb_rcv_nxt) 1; 
                              tcb_rcv_wnd := tcb3.(tcb_rcv_wnd); tcb_rcv_up := tcb3.(tcb_rcv_up);
                              tcb_irs := tcb3.(tcb_irs); tcb_rcv_queue := tcb3.(tcb_rcv_queue);
                              tcb_retrans_queue := tcb3.(tcb_retrans_queue);
                              tcb_cwnd := tcb3.(tcb_cwnd); tcb_ssthresh := tcb3.(tcb_ssthresh); 
                              tcb_dupacks := tcb3.(tcb_dupacks); tcb_recover := tcb3.(tcb_recover);
                              tcb_srtt := tcb3.(tcb_srtt); tcb_rttvar := tcb3.(tcb_rttvar); 
                              tcb_rto := tcb3.(tcb_rto); tcb_backoff := tcb3.(tcb_backoff);
                              tcb_retransmit_timer := tcb3.(tcb_retransmit_timer); 
                              tcb_persist_timer := tcb3.(tcb_persist_timer);
                              tcb_keepalive_timer := tcb3.(tcb_keepalive_timer); 
                              tcb_time_wait_timer := tcb3.(tcb_time_wait_timer); 
                              tcb_delack_timer := tcb3.(tcb_delack_timer);
                              tcb_mss := tcb3.(tcb_mss); tcb_window_scale := tcb3.(tcb_window_scale); 
                              tcb_sack_permitted := tcb3.(tcb_sack_permitted); 
                              tcb_timestamps := tcb3.(tcb_timestamps);
                              tcb_last_ack_sent := tcb3.(tcb_last_ack_sent); 
                              tcb_fin_sent := tcb3.(tcb_fin_sent); tcb_fin_rcvd := true |} in
               (tcb4, Some (generate_ack tcb4), Some payload)
             else (tcb3, None, Some payload)
             
       | FIN_WAIT_1 =>
           if is_ack_segment seg && ack_acceptable tcb seg.(tcp_ack) then
             if tcb.(tcb_fin_sent) && seq_geq seg.(tcp_ack) tcb.(tcb_snd_nxt) then
               if is_fin_segment seg then
                 let tcb' := {| tcb_local_addr := tcb.(tcb_local_addr);
                                tcb_remote_addr := tcb.(tcb_remote_addr);
                                tcb_local_port := tcb.(tcb_local_port);
                                tcb_remote_port := tcb.(tcb_remote_port);
                                tcb_state := TIME_WAIT;
                                tcb_snd_una := seg.(tcp_ack); tcb_snd_nxt := tcb.(tcb_snd_nxt); 
                                tcb_snd_wnd := seg.(tcp_window);
                                tcb_snd_up := tcb.(tcb_snd_up); tcb_snd_wl1 := seg.(tcp_seq); 
                                tcb_snd_wl2 := seg.(tcp_ack);
                                tcb_iss := tcb.(tcb_iss);
                                tcb_rcv_nxt := seq_add tcb.(tcb_rcv_nxt) 1; 
                                tcb_rcv_wnd := tcb.(tcb_rcv_wnd); tcb_rcv_up := tcb.(tcb_rcv_up);
                                tcb_irs := tcb.(tcb_irs); tcb_rcv_queue := [];
                                tcb_retrans_queue := [];
                                tcb_cwnd := tcb.(tcb_cwnd); tcb_ssthresh := tcb.(tcb_ssthresh); 
                                tcb_dupacks := 0; tcb_recover := tcb.(tcb_recover);
                                tcb_srtt := tcb.(tcb_srtt); tcb_rttvar := tcb.(tcb_rttvar); 
                                tcb_rto := tcb.(tcb_rto); tcb_backoff := tcb.(tcb_backoff);
                                tcb_retransmit_timer := None; tcb_persist_timer := None;
                                tcb_keepalive_timer := None; 
                                tcb_time_wait_timer := Some (2 * MSL); 
                                tcb_delack_timer := None;
                                tcb_mss := tcb.(tcb_mss); tcb_window_scale := tcb.(tcb_window_scale); 
                                tcb_sack_permitted := tcb.(tcb_sack_permitted); 
                                tcb_timestamps := tcb.(tcb_timestamps);
                                tcb_last_ack_sent := tcb.(tcb_last_ack_sent); 
                                tcb_fin_sent := true; tcb_fin_rcvd := true |} in
                 (tcb', Some (generate_ack tcb'), None)
               else
                 let tcb' := {| tcb_local_addr := tcb.(tcb_local_addr);
                                tcb_remote_addr := tcb.(tcb_remote_addr);
                                tcb_local_port := tcb.(tcb_local_port);
                                tcb_remote_port := tcb.(tcb_remote_port);
                                tcb_state := FIN_WAIT_2;
                                tcb_snd_una := seg.(tcp_ack); tcb_snd_nxt := tcb.(tcb_snd_nxt); 
                                tcb_snd_wnd := seg.(tcp_window);
                                tcb_snd_up := tcb.(tcb_snd_up); tcb_snd_wl1 := seg.(tcp_seq); 
                                tcb_snd_wl2 := seg.(tcp_ack);
                                tcb_iss := tcb.(tcb_iss);
                                tcb_rcv_nxt := tcb.(tcb_rcv_nxt); tcb_rcv_wnd := tcb.(tcb_rcv_wnd); 
                                tcb_rcv_up := tcb.(tcb_rcv_up);
                                tcb_irs := tcb.(tcb_irs); tcb_rcv_queue := tcb.(tcb_rcv_queue);
                                tcb_retrans_queue := [];
                                tcb_cwnd := tcb.(tcb_cwnd); tcb_ssthresh := tcb.(tcb_ssthresh); 
                                tcb_dupacks := 0; tcb_recover := tcb.(tcb_recover);
                                tcb_srtt := tcb.(tcb_srtt); tcb_rttvar := tcb.(tcb_rttvar); 
                                tcb_rto := tcb.(tcb_rto); tcb_backoff := tcb.(tcb_backoff);
                                tcb_retransmit_timer := None; tcb_persist_timer := None;
                                tcb_keepalive_timer := None; tcb_time_wait_timer := None; 
                                tcb_delack_timer := None;
                                tcb_mss := tcb.(tcb_mss); tcb_window_scale := tcb.(tcb_window_scale); 
                                tcb_sack_permitted := tcb.(tcb_sack_permitted); 
                                tcb_timestamps := tcb.(tcb_timestamps);
                                tcb_last_ack_sent := tcb.(tcb_last_ack_sent); 
                                tcb_fin_sent := true; tcb_fin_rcvd := false |} in
                 (tcb', None, None)
             else if is_fin_segment seg then
               let tcb' := {| tcb_local_addr := tcb.(tcb_local_addr);
                              tcb_remote_addr := tcb.(tcb_remote_addr);
                              tcb_local_port := tcb.(tcb_local_port);
                              tcb_remote_port := tcb.(tcb_remote_port);
                              tcb_state := CLOSING;
                              tcb_snd_una := tcb.(tcb_snd_una); tcb_snd_nxt := tcb.(tcb_snd_nxt); 
                              tcb_snd_wnd := tcb.(tcb_snd_wnd);
                              tcb_snd_up := tcb.(tcb_snd_up); tcb_snd_wl1 := tcb.(tcb_snd_wl1); 
                              tcb_snd_wl2 := tcb.(tcb_snd_wl2);
                              tcb_iss := tcb.(tcb_iss);
                              tcb_rcv_nxt := seq_add tcb.(tcb_rcv_nxt) 1; 
                              tcb_rcv_wnd := tcb.(tcb_rcv_wnd); tcb_rcv_up := tcb.(tcb_rcv_up);
                              tcb_irs := tcb.(tcb_irs); tcb_rcv_queue := [];
                              tcb_retrans_queue := tcb.(tcb_retrans_queue);
                              tcb_cwnd := tcb.(tcb_cwnd); tcb_ssthresh := tcb.(tcb_ssthresh); 
                              tcb_dupacks := 0; tcb_recover := tcb.(tcb_recover);
                              tcb_srtt := tcb.(tcb_srtt); tcb_rttvar := tcb.(tcb_rttvar); 
                              tcb_rto := tcb.(tcb_rto); tcb_backoff := tcb.(tcb_backoff);
                              tcb_retransmit_timer := tcb.(tcb_retransmit_timer); 
                              tcb_persist_timer := tcb.(tcb_persist_timer);
                              tcb_keepalive_timer := tcb.(tcb_keepalive_timer); 
                              tcb_time_wait_timer := None; tcb_delack_timer := None;
                              tcb_mss := tcb.(tcb_mss); tcb_window_scale := tcb.(tcb_window_scale); 
                              tcb_sack_permitted := tcb.(tcb_sack_permitted); 
                              tcb_timestamps := tcb.(tcb_timestamps);
                              tcb_last_ack_sent := tcb.(tcb_last_ack_sent); 
                              tcb_fin_sent := true; tcb_fin_rcvd := true |} in
               (tcb', Some (generate_ack tcb'), None)
             else (tcb, None, None)
           else (tcb, None, None)
           
       | FIN_WAIT_2 =>
           if is_fin_segment seg then
             let tcb' := {| tcb_local_addr := tcb.(tcb_local_addr);
                            tcb_remote_addr := tcb.(tcb_remote_addr);
                            tcb_local_port := tcb.(tcb_local_port);
                            tcb_remote_port := tcb.(tcb_remote_port);
                            tcb_state := TIME_WAIT;
                            tcb_snd_una := tcb.(tcb_snd_una); tcb_snd_nxt := tcb.(tcb_snd_nxt); 
                            tcb_snd_wnd := tcb.(tcb_snd_wnd);
                            tcb_snd_up := tcb.(tcb_snd_up); tcb_snd_wl1 := tcb.(tcb_snd_wl1); 
                            tcb_snd_wl2 := tcb.(tcb_snd_wl2);
                            tcb_iss := tcb.(tcb_iss);
                            tcb_rcv_nxt := seq_add tcb.(tcb_rcv_nxt) 1; 
                            tcb_rcv_wnd := tcb.(tcb_rcv_wnd); tcb_rcv_up := tcb.(tcb_rcv_up);
                            tcb_irs := tcb.(tcb_irs); tcb_rcv_queue := [];
                            tcb_retrans_queue := [];
                            tcb_cwnd := tcb.(tcb_cwnd); tcb_ssthresh := tcb.(tcb_ssthresh); 
                            tcb_dupacks := 0; tcb_recover := tcb.(tcb_recover);
                            tcb_srtt := tcb.(tcb_srtt); tcb_rttvar := tcb.(tcb_rttvar); 
                            tcb_rto := tcb.(tcb_rto); tcb_backoff := tcb.(tcb_backoff);
                            tcb_retransmit_timer := None; tcb_persist_timer := None;
                            tcb_keepalive_timer := None; 
                            tcb_time_wait_timer := Some (2 * MSL); 
                            tcb_delack_timer := None;
                            tcb_mss := tcb.(tcb_mss); tcb_window_scale := tcb.(tcb_window_scale); 
                            tcb_sack_permitted := tcb.(tcb_sack_permitted); 
                            tcb_timestamps := tcb.(tcb_timestamps);
                            tcb_last_ack_sent := tcb.(tcb_last_ack_sent); 
                            tcb_fin_sent := true; tcb_fin_rcvd := true |} in
             (tcb', Some (generate_ack tcb'), None)
           else (tcb, None, None)
           
       | CLOSE_WAIT =>
           (* Application close causes transition to LAST_ACK, handled elsewhere *)
           (tcb, None, None)
           
       | CLOSING =>
           if is_ack_segment seg && ack_acceptable tcb seg.(tcp_ack) then
             let tcb' := {| tcb_local_addr := tcb.(tcb_local_addr);
                            tcb_remote_addr := tcb.(tcb_remote_addr);
                            tcb_local_port := tcb.(tcb_local_port);
                            tcb_remote_port := tcb.(tcb_remote_port);
                            tcb_state := TIME_WAIT;
                            tcb_snd_una := seg.(tcp_ack); tcb_snd_nxt := tcb.(tcb_snd_nxt); 
                            tcb_snd_wnd := seg.(tcp_window);
                            tcb_snd_up := tcb.(tcb_snd_up); tcb_snd_wl1 := seg.(tcp_seq); 
                            tcb_snd_wl2 := seg.(tcp_ack);
                            tcb_iss := tcb.(tcb_iss);
                            tcb_rcv_nxt := tcb.(tcb_rcv_nxt); tcb_rcv_wnd := tcb.(tcb_rcv_wnd); 
                            tcb_rcv_up := tcb.(tcb_rcv_up);
                            tcb_irs := tcb.(tcb_irs); tcb_rcv_queue := [];
                            tcb_retrans_queue := [];
                            tcb_cwnd := tcb.(tcb_cwnd); tcb_ssthresh := tcb.(tcb_ssthresh); 
                            tcb_dupacks := 0; tcb_recover := tcb.(tcb_recover);
                            tcb_srtt := tcb.(tcb_srtt); tcb_rttvar := tcb.(tcb_rttvar); 
                            tcb_rto := tcb.(tcb_rto); tcb_backoff := tcb.(tcb_backoff);
                            tcb_retransmit_timer := None; tcb_persist_timer := None;
                            tcb_keepalive_timer := None; 
                            tcb_time_wait_timer := Some (2 * MSL); 
                            tcb_delack_timer := None;
                            tcb_mss := tcb.(tcb_mss); tcb_window_scale := tcb.(tcb_window_scale); 
                            tcb_sack_permitted := tcb.(tcb_sack_permitted); 
                            tcb_timestamps := tcb.(tcb_timestamps);
                            tcb_last_ack_sent := tcb.(tcb_last_ack_sent); 
                            tcb_fin_sent := true; tcb_fin_rcvd := true |} in
             (tcb', None, None)
           else (tcb, None, None)
           
       | LAST_ACK =>
           if is_ack_segment seg && ack_acceptable tcb seg.(tcp_ack) then
             ({| tcb_local_addr := tcb.(tcb_local_addr);
                 tcb_remote_addr := tcb.(tcb_remote_addr);
                 tcb_local_port := tcb.(tcb_local_port);
                 tcb_remote_port := tcb.(tcb_remote_port);
                 tcb_state := CLOSED;
                 tcb_snd_una := tcb.(tcb_snd_una); tcb_snd_nxt := tcb.(tcb_snd_nxt); 
                 tcb_snd_wnd := tcb.(tcb_snd_wnd);
                 tcb_snd_up := tcb.(tcb_snd_up); tcb_snd_wl1 := tcb.(tcb_snd_wl1); 
                 tcb_snd_wl2 := tcb.(tcb_snd_wl2);
                 tcb_iss := tcb.(tcb_iss);
                 tcb_rcv_nxt := tcb.(tcb_rcv_nxt); tcb_rcv_wnd := tcb.(tcb_rcv_wnd); 
                 tcb_rcv_up := tcb.(tcb_rcv_up);
                 tcb_irs := tcb.(tcb_irs); tcb_rcv_queue := [];
                 tcb_retrans_queue := [];
                 tcb_cwnd := INITIAL_CWND; tcb_ssthresh := INITIAL_SSTHRESH; 
                 tcb_dupacks := 0; tcb_recover := 0;
                 tcb_srtt := 0; tcb_rttvar := 0; tcb_rto := INITIAL_RTO; tcb_backoff := 1;
                 tcb_retransmit_timer := None; tcb_persist_timer := None;
                 tcb_keepalive_timer := None; tcb_time_wait_timer := None; 
                 tcb_delack_timer := None;
                 tcb_mss := tcb.(tcb_mss); tcb_window_scale := tcb.(tcb_window_scale); 
                 tcb_sack_permitted := tcb.(tcb_sack_permitted); 
                 tcb_timestamps := tcb.(tcb_timestamps);
                 tcb_last_ack_sent := tcb.(tcb_last_ack_sent); 
                 tcb_fin_sent := false; tcb_fin_rcvd := false |}, None, None)
           else (tcb, None, None)
           
       | TIME_WAIT =>
           (* Only RST segments processed, wait for timeout *)
           if is_rst_segment seg then
             ({| tcb_local_addr := tcb.(tcb_local_addr);
                 tcb_remote_addr := tcb.(tcb_remote_addr);
                 tcb_local_port := tcb.(tcb_local_port);
                 tcb_remote_port := tcb.(tcb_remote_port);
                 tcb_state := CLOSED;
                 tcb_snd_una := tcb.(tcb_snd_una); tcb_snd_nxt := tcb.(tcb_snd_nxt); 
                 tcb_snd_wnd := tcb.(tcb_snd_wnd);
                 tcb_snd_up := tcb.(tcb_snd_up); tcb_snd_wl1 := tcb.(tcb_snd_wl1); 
                 tcb_snd_wl2 := tcb.(tcb_snd_wl2);
                 tcb_iss := tcb.(tcb_iss);
                 tcb_rcv_nxt := tcb.(tcb_rcv_nxt); tcb_rcv_wnd := tcb.(tcb_rcv_wnd); 
                 tcb_rcv_up := tcb.(tcb_rcv_up);
                 tcb_irs := tcb.(tcb_irs); tcb_rcv_queue := [];
                 tcb_retrans_queue := [];
                 tcb_cwnd := INITIAL_CWND; tcb_ssthresh := INITIAL_SSTHRESH; 
                 tcb_dupacks := 0; tcb_recover := 0;
                 tcb_srtt := 0; tcb_rttvar := 0; tcb_rto := INITIAL_RTO; tcb_backoff := 1;
                 tcb_retransmit_timer := None; tcb_persist_timer := None;
                 tcb_keepalive_timer := None; tcb_time_wait_timer := None; 
                 tcb_delack_timer := None;
                 tcb_mss := tcb.(tcb_mss); tcb_window_scale := tcb.(tcb_window_scale); 
                 tcb_sack_permitted := tcb.(tcb_sack_permitted); 
                 tcb_timestamps := tcb.(tcb_timestamps);
                 tcb_last_ack_sent := tcb.(tcb_last_ack_sent); 
                 tcb_fin_sent := false; tcb_fin_rcvd := false |}, None, None)
           else (tcb, None, None)
       end.

(* =============================================================================
   Section 14: Retransmission Timer Handler
   ============================================================================= *)

Definition handle_retransmit_timeout (tcb : TCB) : TCB * option TCPHeader :=
  match tcb.(tcb_retrans_queue) with
  | [] => (tcb, None)
  | entry :: _ =>
      (* Retransmit oldest unacked segment *)
      let retrans_hdr := {| tcp_src_port := tcb.(tcb_local_port);
                            tcp_dst_port := tcb.(tcb_remote_port);
                            tcp_seq := entry.(re_seq);
                            tcp_ack := tcb.(tcb_rcv_nxt);
                            tcp_data_offset := 5;
                            tcp_reserved := 0;
                            tcp_flags := set_flag 0 FLAG_ACK;
                            tcp_window := tcb.(tcb_rcv_wnd);
                            tcp_checksum := 0;
                            tcp_urgent := 0;
                            tcp_options := [] |} in
      (* Apply exponential backoff and enter loss recovery *)
      let tcb1 := exponential_backoff_rto tcb in
      let tcb2 := enter_loss_recovery tcb1 in
      (tcb2, Some retrans_hdr)
  end.
  
(* =============================================================================
   Section 15: RTT Measurement and Sampling (RFC 6298)
   ============================================================================= *)

Record RTTSample := {
  rtt_seq : SeqNum;           (* Sequence number being timed *)
  rtt_time : N;               (* Timestamp when sent *)
  rtt_retransmitted : bool   (* Don't sample if retransmitted *)
}.

Definition update_rtt_measurement (tcb : TCB) (ack : AckNum) (current_time : N) 
                                  (sample : option RTTSample) : TCB :=
  match sample with
  | None => tcb
  | Some s =>
      if andb (seq_leq s.(rtt_seq) ack) (negb s.(rtt_retransmitted)) then
        let measured_rtt := current_time - s.(rtt_time) in
        let alpha := 125 in  (* 1/8 in fixed point *)
        let beta := 250 in   (* 1/4 in fixed point *)
        let rttvar' := if N.eqb tcb.(tcb_srtt) 0 then
                         measured_rtt / 2
                       else
                         ((1000 - beta) * tcb.(tcb_rttvar) + 
                          beta * (if N.ltb tcb.(tcb_srtt) measured_rtt 
                                 then measured_rtt - tcb.(tcb_srtt)
                                 else tcb.(tcb_srtt) - measured_rtt)) / 1000 in
        let srtt' := if N.eqb tcb.(tcb_srtt) 0 then
                       measured_rtt
                     else
                       ((1000 - alpha) * tcb.(tcb_srtt) + alpha * measured_rtt) / 1000 in
        let rto' := N.max MIN_RTO (N.min MAX_RTO (srtt' + N.max (4 * rttvar') 1000)) in
        {| tcb_local_addr := tcb.(tcb_local_addr);
           tcb_remote_addr := tcb.(tcb_remote_addr);
           tcb_local_port := tcb.(tcb_local_port);
           tcb_remote_port := tcb.(tcb_remote_port);
           tcb_state := tcb.(tcb_state);
           tcb_snd_una := tcb.(tcb_snd_una);
           tcb_snd_nxt := tcb.(tcb_snd_nxt);
           tcb_snd_wnd := tcb.(tcb_snd_wnd);
           tcb_snd_up := tcb.(tcb_snd_up);
           tcb_snd_wl1 := tcb.(tcb_snd_wl1);
           tcb_snd_wl2 := tcb.(tcb_snd_wl2);
           tcb_iss := tcb.(tcb_iss);
           tcb_rcv_nxt := tcb.(tcb_rcv_nxt);
           tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
           tcb_rcv_up := tcb.(tcb_rcv_up);
           tcb_irs := tcb.(tcb_irs);
           tcb_rcv_queue := tcb.(tcb_rcv_queue);
           tcb_retrans_queue := tcb.(tcb_retrans_queue);
           tcb_cwnd := tcb.(tcb_cwnd);
           tcb_ssthresh := tcb.(tcb_ssthresh);
           tcb_dupacks := tcb.(tcb_dupacks);
           tcb_recover := tcb.(tcb_recover);
           tcb_srtt := srtt';
           tcb_rttvar := rttvar';
           tcb_rto := rto';
           tcb_backoff := tcb.(tcb_backoff);
           tcb_retransmit_timer := tcb.(tcb_retransmit_timer);
           tcb_persist_timer := tcb.(tcb_persist_timer);
           tcb_keepalive_timer := tcb.(tcb_keepalive_timer);
           tcb_time_wait_timer := tcb.(tcb_time_wait_timer);
           tcb_delack_timer := tcb.(tcb_delack_timer);
           tcb_mss := tcb.(tcb_mss);
           tcb_window_scale := tcb.(tcb_window_scale);
           tcb_sack_permitted := tcb.(tcb_sack_permitted);
           tcb_timestamps := tcb.(tcb_timestamps);
           tcb_last_ack_sent := tcb.(tcb_last_ack_sent);
           tcb_fin_sent := tcb.(tcb_fin_sent);
           tcb_fin_rcvd := tcb.(tcb_fin_rcvd) |}
      else tcb
  end.

(* Enhanced TCB needs RTT sampling field *)
(* Add this field to the TCB record: tcb_rtt_sample : option RTTSample *)

(* =============================================================================
   Section 16: Persist Timer (RFC 9293 Section 3.8.6.1)
   ============================================================================= *)

Definition start_persist_timer (tcb : TCB) : TCB :=
  if N.eqb tcb.(tcb_snd_wnd) 0 then
    {| tcb_local_addr := tcb.(tcb_local_addr);
       tcb_remote_addr := tcb.(tcb_remote_addr);
       tcb_local_port := tcb.(tcb_local_port);
       tcb_remote_port := tcb.(tcb_remote_port);
       tcb_state := tcb.(tcb_state);
       tcb_snd_una := tcb.(tcb_snd_una);
       tcb_snd_nxt := tcb.(tcb_snd_nxt);
       tcb_snd_wnd := tcb.(tcb_snd_wnd);
       tcb_snd_up := tcb.(tcb_snd_up);
       tcb_snd_wl1 := tcb.(tcb_snd_wl1);
       tcb_snd_wl2 := tcb.(tcb_snd_wl2);
       tcb_iss := tcb.(tcb_iss);
       tcb_rcv_nxt := tcb.(tcb_rcv_nxt);
       tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
       tcb_rcv_up := tcb.(tcb_rcv_up);
       tcb_irs := tcb.(tcb_irs);
       tcb_rcv_queue := tcb.(tcb_rcv_queue);
       tcb_retrans_queue := tcb.(tcb_retrans_queue);
       tcb_cwnd := tcb.(tcb_cwnd);
       tcb_ssthresh := tcb.(tcb_ssthresh);
       tcb_dupacks := tcb.(tcb_dupacks);
       tcb_recover := tcb.(tcb_recover);
       tcb_srtt := tcb.(tcb_srtt);
       tcb_rttvar := tcb.(tcb_rttvar);
       tcb_rto := tcb.(tcb_rto);
       tcb_backoff := tcb.(tcb_backoff);
       tcb_retransmit_timer := tcb.(tcb_retransmit_timer);
       tcb_persist_timer := Some (N.max tcb.(tcb_rto) 5000);
       tcb_keepalive_timer := tcb.(tcb_keepalive_timer);
       tcb_time_wait_timer := tcb.(tcb_time_wait_timer);
       tcb_delack_timer := tcb.(tcb_delack_timer);
       tcb_mss := tcb.(tcb_mss);
       tcb_window_scale := tcb.(tcb_window_scale);
       tcb_sack_permitted := tcb.(tcb_sack_permitted);
       tcb_timestamps := tcb.(tcb_timestamps);
       tcb_last_ack_sent := tcb.(tcb_last_ack_sent);
       tcb_fin_sent := tcb.(tcb_fin_sent);
       tcb_fin_rcvd := tcb.(tcb_fin_rcvd) |}
  else tcb.

Definition handle_persist_timeout (tcb : TCB) : TCB * option TCPHeader :=
  (* Send zero window probe - 1 byte of data or just the sequence number *)
  let probe_seg := {| tcp_src_port := tcb.(tcb_local_port);
                      tcp_dst_port := tcb.(tcb_remote_port);
                      tcp_seq := tcb.(tcb_snd_una);
                      tcp_ack := tcb.(tcb_rcv_nxt);
                      tcp_data_offset := 5;
                      tcp_reserved := 0;
                      tcp_flags := set_flag 0 FLAG_ACK;
                      tcp_window := tcb.(tcb_rcv_wnd);
                      tcp_checksum := 0;
                      tcp_urgent := 0;
                      tcp_options := [] |} in
  (* Exponentially back off persist timer *)
  let new_persist := match tcb.(tcb_persist_timer) with
                     | None => Some 5000
                     | Some t => Some (N.min (t * 2) 60000)
                     end in
  ({| tcb_local_addr := tcb.(tcb_local_addr);
      tcb_remote_addr := tcb.(tcb_remote_addr);
      tcb_local_port := tcb.(tcb_local_port);
      tcb_remote_port := tcb.(tcb_remote_port);
      tcb_state := tcb.(tcb_state);
      tcb_snd_una := tcb.(tcb_snd_una);
      tcb_snd_nxt := tcb.(tcb_snd_nxt);
      tcb_snd_wnd := tcb.(tcb_snd_wnd);
      tcb_snd_up := tcb.(tcb_snd_up);
      tcb_snd_wl1 := tcb.(tcb_snd_wl1);
      tcb_snd_wl2 := tcb.(tcb_snd_wl2);
      tcb_iss := tcb.(tcb_iss);
      tcb_rcv_nxt := tcb.(tcb_rcv_nxt);
      tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
      tcb_rcv_up := tcb.(tcb_rcv_up);
      tcb_irs := tcb.(tcb_irs);
      tcb_rcv_queue := tcb.(tcb_rcv_queue);
      tcb_retrans_queue := tcb.(tcb_retrans_queue);
      tcb_cwnd := tcb.(tcb_cwnd);
      tcb_ssthresh := tcb.(tcb_ssthresh);
      tcb_dupacks := tcb.(tcb_dupacks);
      tcb_recover := tcb.(tcb_recover);
      tcb_srtt := tcb.(tcb_srtt);
      tcb_rttvar := tcb.(tcb_rttvar);
      tcb_rto := tcb.(tcb_rto);
      tcb_backoff := tcb.(tcb_backoff);
      tcb_retransmit_timer := tcb.(tcb_retransmit_timer);
      tcb_persist_timer := new_persist;
      tcb_keepalive_timer := tcb.(tcb_keepalive_timer);
      tcb_time_wait_timer := tcb.(tcb_time_wait_timer);
      tcb_delack_timer := tcb.(tcb_delack_timer);
      tcb_mss := tcb.(tcb_mss);
      tcb_window_scale := tcb.(tcb_window_scale);
      tcb_sack_permitted := tcb.(tcb_sack_permitted);
      tcb_timestamps := tcb.(tcb_timestamps);
      tcb_last_ack_sent := tcb.(tcb_last_ack_sent);
      tcb_fin_sent := tcb.(tcb_fin_sent);
      tcb_fin_rcvd := tcb.(tcb_fin_rcvd) |}, Some probe_seg).

(* =============================================================================
   Section 17: Simultaneous Open and Close (RFC 9293 Section 3.5)
   ============================================================================= *)

Definition handle_simultaneous_open (tcb : TCB) (seg : TCPHeader) : TCB * option TCPHeader :=
  match tcb.(tcb_state) with
  | SYN_SENT =>
      if andb (is_syn_segment seg) (negb (is_ack_segment seg)) then
        (* Simultaneous open - both sides sent SYN *)
        let tcb' := {| tcb_local_addr := tcb.(tcb_local_addr);
                       tcb_remote_addr := tcb.(tcb_remote_addr);
                       tcb_local_port := tcb.(tcb_local_port);
                       tcb_remote_port := tcb.(tcb_remote_port);
                       tcb_state := SYN_RECEIVED;
                       tcb_snd_una := tcb.(tcb_snd_una);
                       tcb_snd_nxt := tcb.(tcb_snd_nxt);
                       tcb_snd_wnd := tcb.(tcb_snd_wnd);
                       tcb_snd_up := tcb.(tcb_snd_up);
                       tcb_snd_wl1 := seg.(tcp_seq);
                       tcb_snd_wl2 := seg.(tcp_seq);
                       tcb_iss := tcb.(tcb_iss);
                       tcb_rcv_nxt := seq_add seg.(tcp_seq) 1;
                       tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
                       tcb_rcv_up := tcb.(tcb_rcv_up);
                       tcb_irs := seg.(tcp_seq);
                       tcb_rcv_queue := tcb.(tcb_rcv_queue);
                       tcb_retrans_queue := tcb.(tcb_retrans_queue);
                       tcb_cwnd := INITIAL_CWND;
                       tcb_ssthresh := INITIAL_SSTHRESH;
                       tcb_dupacks := 0;
                       tcb_recover := 0;
                       tcb_srtt := 0;
                       tcb_rttvar := 0;
                       tcb_rto := INITIAL_RTO;
                       tcb_backoff := 1;
                       tcb_retransmit_timer := Some INITIAL_RTO;
                       tcb_persist_timer := None;
                       tcb_keepalive_timer := None;
                       tcb_time_wait_timer := None;
                       tcb_delack_timer := None;
                       tcb_mss := tcb.(tcb_mss);
                       tcb_window_scale := tcb.(tcb_window_scale);
                       tcb_sack_permitted := tcb.(tcb_sack_permitted);
                       tcb_timestamps := tcb.(tcb_timestamps);
                       tcb_last_ack_sent := seg.(tcp_seq);
                       tcb_fin_sent := false;
                       tcb_fin_rcvd := false |} in
        let syn_ack := {| tcp_src_port := tcb'.(tcb_local_port);
                          tcp_dst_port := tcb'.(tcb_remote_port);
                          tcp_seq := tcb.(tcb_iss);
                          tcp_ack := tcb'.(tcb_rcv_nxt);
                          tcp_data_offset := 5;
                          tcp_reserved := 0;
                          tcp_flags := set_flag (set_flag 0 FLAG_SYN) FLAG_ACK;
                          tcp_window := tcb'.(tcb_rcv_wnd);
                          tcp_checksum := 0;
                          tcp_urgent := 0;
                          tcp_options := [] |} in
        (tcb', Some syn_ack)
      else
        (tcb, None)
  | _ => (tcb, None)
  end.

Definition handle_simultaneous_close (tcb : TCB) (seg : TCPHeader) : TCB * option TCPHeader :=
  match tcb.(tcb_state) with
  | FIN_WAIT_1 =>
      if andb (is_fin_segment seg) (negb (is_ack_segment seg)) then
        (* Simultaneous close - both sides sent FIN *)
        let tcb' := {| tcb_local_addr := tcb.(tcb_local_addr);
                       tcb_remote_addr := tcb.(tcb_remote_addr);
                       tcb_local_port := tcb.(tcb_local_port);
                       tcb_remote_port := tcb.(tcb_remote_port);
                       tcb_state := CLOSING;
                       tcb_snd_una := tcb.(tcb_snd_una);
                       tcb_snd_nxt := tcb.(tcb_snd_nxt);
                       tcb_snd_wnd := tcb.(tcb_snd_wnd);
                       tcb_snd_up := tcb.(tcb_snd_up);
                       tcb_snd_wl1 := tcb.(tcb_snd_wl1);
                       tcb_snd_wl2 := tcb.(tcb_snd_wl2);
                       tcb_iss := tcb.(tcb_iss);
                       tcb_rcv_nxt := seq_add tcb.(tcb_rcv_nxt) 1;
                       tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
                       tcb_rcv_up := tcb.(tcb_rcv_up);
                       tcb_irs := tcb.(tcb_irs);
                       tcb_rcv_queue := tcb.(tcb_rcv_queue);
                       tcb_retrans_queue := tcb.(tcb_retrans_queue);
                       tcb_cwnd := tcb.(tcb_cwnd);
                       tcb_ssthresh := tcb.(tcb_ssthresh);
                       tcb_dupacks := tcb.(tcb_dupacks);
                       tcb_recover := tcb.(tcb_recover);
                       tcb_srtt := tcb.(tcb_srtt);
                       tcb_rttvar := tcb.(tcb_rttvar);
                       tcb_rto := tcb.(tcb_rto);
                       tcb_backoff := tcb.(tcb_backoff);
                       tcb_retransmit_timer := tcb.(tcb_retransmit_timer);
                       tcb_persist_timer := tcb.(tcb_persist_timer);
                       tcb_keepalive_timer := tcb.(tcb_keepalive_timer);
                       tcb_time_wait_timer := None;
                       tcb_delack_timer := None;
                       tcb_mss := tcb.(tcb_mss);
                       tcb_window_scale := tcb.(tcb_window_scale);
                       tcb_sack_permitted := tcb.(tcb_sack_permitted);
                       tcb_timestamps := tcb.(tcb_timestamps);
                       tcb_last_ack_sent := tcb.(tcb_last_ack_sent);
                       tcb_fin_sent := true;
                       tcb_fin_rcvd := true |} in
        (tcb', Some (generate_ack tcb'))
      else
        (tcb, None)
  | _ => (tcb, None)
  end.

(* =============================================================================
   Section 18: User API Events (RFC 9293 Section 3.9)
   ============================================================================= *)

Inductive UserEvent :=
  | USER_OPEN_ACTIVE : word32 -> word16 -> UserEvent  (* remote addr, port *)
  | USER_OPEN_PASSIVE : UserEvent
  | USER_SEND : list byte -> UserEvent
  | USER_RECEIVE : N -> UserEvent                      (* buffer size *)
  | USER_CLOSE : UserEvent
  | USER_ABORT : UserEvent
  | USER_STATUS : UserEvent.

Definition handle_user_close (tcb : TCB) : TCB * option TCPHeader :=
  match tcb.(tcb_state) with
  | ESTABLISHED =>
      let fin_seg := {| tcp_src_port := tcb.(tcb_local_port);
                        tcp_dst_port := tcb.(tcb_remote_port);
                        tcp_seq := tcb.(tcb_snd_nxt);
                        tcp_ack := tcb.(tcb_rcv_nxt);
                        tcp_data_offset := 5;
                        tcp_reserved := 0;
                        tcp_flags := set_flag (set_flag 0 FLAG_FIN) FLAG_ACK;
                        tcp_window := tcb.(tcb_rcv_wnd);
                        tcp_checksum := 0;
                        tcp_urgent := 0;
                        tcp_options := [] |} in
      let tcb' := {| tcb_local_addr := tcb.(tcb_local_addr);
                     tcb_remote_addr := tcb.(tcb_remote_addr);
                     tcb_local_port := tcb.(tcb_local_port);
                     tcb_remote_port := tcb.(tcb_remote_port);
                     tcb_state := FIN_WAIT_1;
                     tcb_snd_una := tcb.(tcb_snd_una);
                     tcb_snd_nxt := seq_add tcb.(tcb_snd_nxt) 1;
                     tcb_snd_wnd := tcb.(tcb_snd_wnd);
                     tcb_snd_up := tcb.(tcb_snd_up);
                     tcb_snd_wl1 := tcb.(tcb_snd_wl1);
                     tcb_snd_wl2 := tcb.(tcb_snd_wl2);
                     tcb_iss := tcb.(tcb_iss);
                     tcb_rcv_nxt := tcb.(tcb_rcv_nxt);
                     tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
                     tcb_rcv_up := tcb.(tcb_rcv_up);
                     tcb_irs := tcb.(tcb_irs);
                     tcb_rcv_queue := tcb.(tcb_rcv_queue);
                     tcb_retrans_queue := tcb.(tcb_retrans_queue);
                     tcb_cwnd := tcb.(tcb_cwnd);
                     tcb_ssthresh := tcb.(tcb_ssthresh);
                     tcb_dupacks := tcb.(tcb_dupacks);
                     tcb_recover := tcb.(tcb_recover);
                     tcb_srtt := tcb.(tcb_srtt);
                     tcb_rttvar := tcb.(tcb_rttvar);
                     tcb_rto := tcb.(tcb_rto);
                     tcb_backoff := tcb.(tcb_backoff);
                     tcb_retransmit_timer := Some tcb.(tcb_rto);
                     tcb_persist_timer := tcb.(tcb_persist_timer);
                     tcb_keepalive_timer := tcb.(tcb_keepalive_timer);
                     tcb_time_wait_timer := None;
                     tcb_delack_timer := tcb.(tcb_delack_timer);
                     tcb_mss := tcb.(tcb_mss);
                     tcb_window_scale := tcb.(tcb_window_scale);
                     tcb_sack_permitted := tcb.(tcb_sack_permitted);
                     tcb_timestamps := tcb.(tcb_timestamps);
                     tcb_last_ack_sent := tcb.(tcb_last_ack_sent);
                     tcb_fin_sent := true;
                     tcb_fin_rcvd := tcb.(tcb_fin_rcvd) |} in
      (tcb', Some fin_seg)
      
  | CLOSE_WAIT =>
      let fin_seg := {| tcp_src_port := tcb.(tcb_local_port);
                        tcp_dst_port := tcb.(tcb_remote_port);
                        tcp_seq := tcb.(tcb_snd_nxt);
                        tcp_ack := tcb.(tcb_rcv_nxt);
                        tcp_data_offset := 5;
                        tcp_reserved := 0;
                        tcp_flags := set_flag (set_flag 0 FLAG_FIN) FLAG_ACK;
                        tcp_window := tcb.(tcb_rcv_wnd);
                        tcp_checksum := 0;
                        tcp_urgent := 0;
                        tcp_options := [] |} in
      let tcb' := {| tcb_local_addr := tcb.(tcb_local_addr);
                     tcb_remote_addr := tcb.(tcb_remote_addr);
                     tcb_local_port := tcb.(tcb_local_port);
                     tcb_remote_port := tcb.(tcb_remote_port);
                     tcb_state := LAST_ACK;
                     tcb_snd_una := tcb.(tcb_snd_una);
                     tcb_snd_nxt := seq_add tcb.(tcb_snd_nxt) 1;
                     tcb_snd_wnd := tcb.(tcb_snd_wnd);
                     tcb_snd_up := tcb.(tcb_snd_up);
                     tcb_snd_wl1 := tcb.(tcb_snd_wl1);
                     tcb_snd_wl2 := tcb.(tcb_snd_wl2);
                     tcb_iss := tcb.(tcb_iss);
                     tcb_rcv_nxt := tcb.(tcb_rcv_nxt);
                     tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
                     tcb_rcv_up := tcb.(tcb_rcv_up);
                     tcb_irs := tcb.(tcb_irs);
                     tcb_rcv_queue := tcb.(tcb_rcv_queue);
                     tcb_retrans_queue := tcb.(tcb_retrans_queue);
                     tcb_cwnd := tcb.(tcb_cwnd);
                     tcb_ssthresh := tcb.(tcb_ssthresh);
                     tcb_dupacks := tcb.(tcb_dupacks);
                     tcb_recover := tcb.(tcb_recover);
                     tcb_srtt := tcb.(tcb_srtt);
                     tcb_rttvar := tcb.(tcb_rttvar);
                     tcb_rto := tcb.(tcb_rto);
                     tcb_backoff := tcb.(tcb_backoff);
                     tcb_retransmit_timer := Some tcb.(tcb_rto);
                     tcb_persist_timer := tcb.(tcb_persist_timer);
                     tcb_keepalive_timer := tcb.(tcb_keepalive_timer);
                     tcb_time_wait_timer := None;
                     tcb_delack_timer := tcb.(tcb_delack_timer);
                     tcb_mss := tcb.(tcb_mss);
                     tcb_window_scale := tcb.(tcb_window_scale);
                     tcb_sack_permitted := tcb.(tcb_sack_permitted);
                     tcb_timestamps := tcb.(tcb_timestamps);
                     tcb_last_ack_sent := tcb.(tcb_last_ack_sent);
                     tcb_fin_sent := true;
                     tcb_fin_rcvd := tcb.(tcb_fin_rcvd) |} in
      (tcb', Some fin_seg)
      
  | _ => (tcb, None)
  end.
  
(* =============================================================================
   Section 19: Complete User API (RFC 9293 Section 3.9)
   ============================================================================= *)

Definition handle_user_open_active (tcb : TCB) (remote_addr : word32) (remote_port : word16) 
                                   (iss : SeqNum) : TCB * option TCPHeader :=
  match tcb.(tcb_state) with
  | CLOSED =>
      let tcb' := {| tcb_local_addr := tcb.(tcb_local_addr);
                     tcb_remote_addr := remote_addr;
                     tcb_local_port := tcb.(tcb_local_port);
                     tcb_remote_port := remote_port;
                     tcb_state := SYN_SENT;
                     tcb_snd_una := iss;
                     tcb_snd_nxt := seq_add iss 1;
                     tcb_snd_wnd := 0;
                     tcb_snd_up := 0;
                     tcb_snd_wl1 := 0;
                     tcb_snd_wl2 := 0;
                     tcb_iss := iss;
                     tcb_rcv_nxt := 0;
                     tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
                     tcb_rcv_up := 0;
                     tcb_irs := 0;
                     tcb_rcv_queue := [];
                     tcb_retrans_queue := [];
                     tcb_cwnd := INITIAL_CWND;
                     tcb_ssthresh := INITIAL_SSTHRESH;
                     tcb_dupacks := 0;
                     tcb_recover := 0;
                     tcb_srtt := 0;
                     tcb_rttvar := 0;
                     tcb_rto := INITIAL_RTO;
                     tcb_backoff := 1;
                     tcb_retransmit_timer := Some INITIAL_RTO;
                     tcb_persist_timer := None;
                     tcb_keepalive_timer := None;
                     tcb_time_wait_timer := None;
                     tcb_delack_timer := None;
                     tcb_mss := DEFAULT_MSS;
                     tcb_window_scale := 0;
                     tcb_sack_permitted := false;
                     tcb_timestamps := false;
                     tcb_last_ack_sent := 0;
                     tcb_fin_sent := false;
                     tcb_fin_rcvd := false |} in
      let syn := {| tcp_src_port := tcb'.(tcb_local_port);
                    tcp_dst_port := remote_port;
                    tcp_seq := iss;
                    tcp_ack := 0;
                    tcp_data_offset := 5;
                    tcp_reserved := 0;
                    tcp_flags := set_flag 0 FLAG_SYN;
                    tcp_window := tcb.(tcb_rcv_wnd);
                    tcp_checksum := 0;
                    tcp_urgent := 0;
                    tcp_options := [] |} in
      (tcb', Some syn)
  | _ => (tcb, None)
  end.

Definition handle_user_open_passive (tcb : TCB) : TCB :=
  match tcb.(tcb_state) with
  | CLOSED =>
      {| tcb_local_addr := tcb.(tcb_local_addr);
         tcb_remote_addr := 0;
         tcb_local_port := tcb.(tcb_local_port);
         tcb_remote_port := 0;
         tcb_state := LISTEN;
         tcb_snd_una := 0;
         tcb_snd_nxt := 0;
         tcb_snd_wnd := 0;
         tcb_snd_up := 0;
         tcb_snd_wl1 := 0;
         tcb_snd_wl2 := 0;
         tcb_iss := tcb.(tcb_iss);
         tcb_rcv_nxt := 0;
         tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
         tcb_rcv_up := 0;
         tcb_irs := 0;
         tcb_rcv_queue := [];
         tcb_retrans_queue := [];
         tcb_cwnd := INITIAL_CWND;
         tcb_ssthresh := INITIAL_SSTHRESH;
         tcb_dupacks := 0;
         tcb_recover := 0;
         tcb_srtt := 0;
         tcb_rttvar := 0;
         tcb_rto := INITIAL_RTO;
         tcb_backoff := 1;
         tcb_retransmit_timer := None;
         tcb_persist_timer := None;
         tcb_keepalive_timer := None;
         tcb_time_wait_timer := None;
         tcb_delack_timer := None;
         tcb_mss := DEFAULT_MSS;
         tcb_window_scale := 0;
         tcb_sack_permitted := false;
         tcb_timestamps := false;
         tcb_last_ack_sent := 0;
         tcb_fin_sent := false;
         tcb_fin_rcvd := false |}
  | _ => tcb
  end.

Definition handle_user_abort (tcb : TCB) : TCB * option TCPHeader :=
  let rst := {| tcp_src_port := tcb.(tcb_local_port);
                tcp_dst_port := tcb.(tcb_remote_port);
                tcp_seq := tcb.(tcb_snd_nxt);
                tcp_ack := 0;
                tcp_data_offset := 5;
                tcp_reserved := 0;
                tcp_flags := set_flag 0 FLAG_RST;
                tcp_window := 0;
                tcp_checksum := 0;
                tcp_urgent := 0;
                tcp_options := [] |} in
  let tcb' := {| tcb_local_addr := tcb.(tcb_local_addr);
                 tcb_remote_addr := tcb.(tcb_remote_addr);
                 tcb_local_port := tcb.(tcb_local_port);
                 tcb_remote_port := tcb.(tcb_remote_port);
                 tcb_state := CLOSED;
                 tcb_snd_una := 0;
                 tcb_snd_nxt := 0;
                 tcb_snd_wnd := 0;
                 tcb_snd_up := 0;
                 tcb_snd_wl1 := 0;
                 tcb_snd_wl2 := 0;
                 tcb_iss := 0;
                 tcb_rcv_nxt := 0;
                 tcb_rcv_wnd := 0;
                 tcb_rcv_up := 0;
                 tcb_irs := 0;
                 tcb_rcv_queue := [];
                 tcb_retrans_queue := [];
                 tcb_cwnd := INITIAL_CWND;
                 tcb_ssthresh := INITIAL_SSTHRESH;
                 tcb_dupacks := 0;
                 tcb_recover := 0;
                 tcb_srtt := 0;
                 tcb_rttvar := 0;
                 tcb_rto := INITIAL_RTO;
                 tcb_backoff := 1;
                 tcb_retransmit_timer := None;
                 tcb_persist_timer := None;
                 tcb_keepalive_timer := None;
                 tcb_time_wait_timer := None;
                 tcb_delack_timer := None;
                 tcb_mss := DEFAULT_MSS;
                 tcb_window_scale := 0;
                 tcb_sack_permitted := false;
                 tcb_timestamps := false;
                 tcb_last_ack_sent := 0;
                 tcb_fin_sent := false;
                 tcb_fin_rcvd := false |} in
  (tcb', Some rst).

(* =============================================================================
   Section 20: Nagle's Algorithm (RFC 1122 Section 4.2.3.4)
   ============================================================================= *)

Definition NAGLE_TIMEOUT : N := 200. (* ms *)

Record SendBuffer := {
  sb_data : list byte;
  sb_seq : SeqNum;
  sb_nagle_timer : option N
}.

Definition should_send_nagle (tcb : TCB) (sb : SendBuffer) : bool :=
  let unacked := N.ltb tcb.(tcb_snd_una) tcb.(tcb_snd_nxt) in
  let full_segment := N.eqb (N.of_nat (length sb.(sb_data))) tcb.(tcb_mss) in
  let no_unacked := negb unacked in
  let timer_expired := match sb.(sb_nagle_timer) with
                       | None => false
                       | Some _ => true
                       end in
  orb full_segment (orb no_unacked timer_expired).

Definition update_nagle_timer (sb : SendBuffer) (should_send : bool) : SendBuffer :=
  if should_send then
    {| sb_data := [];
       sb_seq := sb.(sb_seq);
       sb_nagle_timer := None |}
  else
    {| sb_data := sb.(sb_data);
       sb_seq := sb.(sb_seq);
       sb_nagle_timer := Some NAGLE_TIMEOUT |}.

(* =============================================================================
   Section 21: Silly Window Syndrome Avoidance (RFC 1122 Section 4.2.3.3)
   ============================================================================= *)

Definition MIN_SEGMENT : N := 50. (* Minimum segment to send *)

Definition should_send_sws (tcb : TCB) (data_len : N) : bool :=
  let can_send := N.min data_len tcb.(tcb_snd_wnd) in
  orb (N.eqb can_send data_len)                    (* Can send all data *)
      (orb (N.leb tcb.(tcb_mss) can_send)         (* Can send MSS *)
           (N.leb (tcb.(tcb_snd_wnd) / 2) can_send)). (* Can send half window *)

Definition receiver_sws_check (tcb : TCB) : word16 :=
  let available := tcb.(tcb_rcv_wnd) in
  if orb (N.leb tcb.(tcb_mss) available)
         (N.leb (MAX_WINDOW / 2) available) then
    available
  else
    0. (* Advertise zero window *)

(* =============================================================================
   Section 22: Delayed ACKs (RFC 1122 Section 4.2.3.2)
   ============================================================================= *)

Definition DELACK_TIMEOUT : N := 200. (* ms, max 500ms per RFC *)
Definition DELACK_THRESHOLD : N := 2. (* ACK every 2nd segment *)

Record DelayedAckState := {
  da_pending : N;        (* Number of segments pending ACK *)
  da_timer : option N    (* Delayed ACK timer *)
}.

Definition should_send_immediate_ack (tcb : TCB) (seg : TCPHeader) : bool :=
  orb (is_fin_segment seg)
      (orb (is_syn_segment seg)
           (orb (is_psh_segment seg)
                (N.ltb tcb.(tcb_rcv_wnd) tcb.(tcb_mss)))). (* Small window *)

Definition update_delayed_ack (das : DelayedAckState) (immediate : bool) : DelayedAckState * bool :=
  if immediate then
    ({| da_pending := 0; da_timer := None |}, true)
  else
    let pending' := das.(da_pending) + 1 in
    if N.leb DELACK_THRESHOLD pending' then
      ({| da_pending := 0; da_timer := None |}, true)
    else
      ({| da_pending := pending'; da_timer := Some DELACK_TIMEOUT |}, false).

Definition handle_delack_timeout (das : DelayedAckState) : DelayedAckState * bool :=
  ({| da_pending := 0; da_timer := None |}, true).

(* =============================================================================
   Section 23: Keepalive Processing (RFC 9293 Section 3.8.4)
   ============================================================================= *)

Definition KEEPALIVE_IDLE : N := 7200000.    (* 2 hours in ms *)
Definition KEEPALIVE_INTERVAL : N := 75000.  (* 75 seconds *)
Definition KEEPALIVE_PROBES : N := 9.        (* Max probes before closing *)

Record KeepaliveState := {
  ka_enabled : bool;
  ka_probes_sent : N;
  ka_timer : option N
}.

Definition start_keepalive (kas : KeepaliveState) (tcb : TCB) : KeepaliveState :=
  if andb kas.(ka_enabled) 
         (match tcb.(tcb_state) with ESTABLISHED => true | _ => false end) then
    {| ka_enabled := true;
       ka_probes_sent := 0;
       ka_timer := Some KEEPALIVE_IDLE |}
  else kas.

Definition handle_keepalive_timeout (kas : KeepaliveState) (tcb : TCB) 
                                   : KeepaliveState * TCB * option TCPHeader :=
  if N.ltb kas.(ka_probes_sent) KEEPALIVE_PROBES then
    let probe := {| tcp_src_port := tcb.(tcb_local_port);
                    tcp_dst_port := tcb.(tcb_remote_port);
                    tcp_seq := seq_sub tcb.(tcb_snd_nxt) 1;
                    tcp_ack := tcb.(tcb_rcv_nxt);
                    tcp_data_offset := 5;
                    tcp_reserved := 0;
                    tcp_flags := set_flag 0 FLAG_ACK;
                    tcp_window := tcb.(tcb_rcv_wnd);
                    tcp_checksum := 0;
                    tcp_urgent := 0;
                    tcp_options := [] |} in
    let kas' := {| ka_enabled := kas.(ka_enabled);
                   ka_probes_sent := kas.(ka_probes_sent) + 1;
                   ka_timer := Some KEEPALIVE_INTERVAL |} in
    (kas', tcb, Some probe)
  else
    (* Connection dead, close it *)
    let tcb' := {| tcb_local_addr := tcb.(tcb_local_addr);
                   tcb_remote_addr := tcb.(tcb_remote_addr);
                   tcb_local_port := tcb.(tcb_local_port);
                   tcb_remote_port := tcb.(tcb_remote_port);
                   tcb_state := CLOSED;
                   tcb_snd_una := tcb.(tcb_snd_una);
                   tcb_snd_nxt := tcb.(tcb_snd_nxt);
                   tcb_snd_wnd := tcb.(tcb_snd_wnd);
                   tcb_snd_up := tcb.(tcb_snd_up);
                   tcb_snd_wl1 := tcb.(tcb_snd_wl1);
                   tcb_snd_wl2 := tcb.(tcb_snd_wl2);
                   tcb_iss := tcb.(tcb_iss);
                   tcb_rcv_nxt := tcb.(tcb_rcv_nxt);
                   tcb_rcv_wnd := tcb.(tcb_rcv_wnd);
                   tcb_rcv_up := tcb.(tcb_rcv_up);
                   tcb_irs := tcb.(tcb_irs);
                   tcb_rcv_queue := [];
                   tcb_retrans_queue := [];
                   tcb_cwnd := INITIAL_CWND;
                   tcb_ssthresh := INITIAL_SSTHRESH;
                   tcb_dupacks := 0;
                   tcb_recover := 0;
                   tcb_srtt := 0;
                   tcb_rttvar := 0;
                   tcb_rto := INITIAL_RTO;
                   tcb_backoff := 1;
                   tcb_retransmit_timer := None;
                   tcb_persist_timer := None;
                   tcb_keepalive_timer := None;
                   tcb_time_wait_timer := None;
                   tcb_delack_timer := None;
                   tcb_mss := tcb.(tcb_mss);
                   tcb_window_scale := tcb.(tcb_window_scale);
                   tcb_sack_permitted := tcb.(tcb_sack_permitted);
                   tcb_timestamps := tcb.(tcb_timestamps);
                   tcb_last_ack_sent := tcb.(tcb_last_ack_sent);
                   tcb_fin_sent := false;
                   tcb_fin_rcvd := false |} in
    (kas, tcb', None).

(* =============================================================================
   Section 24: Comprehensive Error Handling
   ============================================================================= *)

Inductive TCPError :=
  | ERR_CONNECTION_REFUSED
  | ERR_CONNECTION_RESET  
  | ERR_CONNECTION_CLOSING
  | ERR_CONNECTION_TIMEOUT
  | ERR_INVALID_STATE
  | ERR_INVALID_SEGMENT
  | ERR_BUFFER_OVERFLOW
  | ERR_NO_ROUTE
  | ERR_ADDRESS_IN_USE.

Definition validate_segment_checksum (pseudo : TCPPseudoHeader) (hdr : TCPHeader) 
                                    (data : list byte) : bool :=
  N.eqb (calculate_tcp_checksum pseudo hdr data) 0.

Definition validate_state_transition (from : TCPState) (to : TCPState) 
                                    (event : UserEvent) : bool :=
  match from, event, to with
  | CLOSED, USER_OPEN_ACTIVE _ _, SYN_SENT => true
  | CLOSED, USER_OPEN_PASSIVE, LISTEN => true
  | LISTEN, _, SYN_RECEIVED => true
  | LISTEN, _, LISTEN => true  (* Can stay in LISTEN *)
  | SYN_SENT, _, ESTABLISHED => true
  | SYN_SENT, _, SYN_RECEIVED => true  (* Simultaneous open *)
  | SYN_SENT, _, CLOSED => true  (* Reset or abort *)
  | SYN_RECEIVED, _, ESTABLISHED => true
  | SYN_RECEIVED, _, LISTEN => true  (* Reset *)
  | SYN_RECEIVED, _, FIN_WAIT_1 => true  (* Close after SYN *)
  | ESTABLISHED, USER_CLOSE, FIN_WAIT_1 => true
  | ESTABLISHED, _, CLOSE_WAIT => true  (* Received FIN *)
  | ESTABLISHED, _, CLOSED => true  (* Reset *)
  | FIN_WAIT_1, _, FIN_WAIT_2 => true
  | FIN_WAIT_1, _, TIME_WAIT => true  (* Simultaneous close *)
  | FIN_WAIT_1, _, CLOSING => true
  | FIN_WAIT_2, _, TIME_WAIT => true
  | CLOSE_WAIT, USER_CLOSE, LAST_ACK => true
  | CLOSING, _, TIME_WAIT => true
  | LAST_ACK, _, CLOSED => true
  | TIME_WAIT, _, CLOSED => true
  | _, _, _ => false  (* Invalid transition *)
  end.

Record ErrorStats := {
  err_checksum_failures : N;
  err_invalid_segments : N;
  err_resets_received : N;
  err_resets_sent : N;
  err_retransmit_timeouts : N;
  err_zero_windows : N
}.

Definition update_error_stats (stats : ErrorStats) (err : TCPError) : ErrorStats :=
  match err with
  | ERR_INVALID_SEGMENT =>
      {| err_checksum_failures := stats.(err_checksum_failures);
         err_invalid_segments := stats.(err_invalid_segments) + 1;
         err_resets_received := stats.(err_resets_received);
         err_resets_sent := stats.(err_resets_sent);
         err_retransmit_timeouts := stats.(err_retransmit_timeouts);
         err_zero_windows := stats.(err_zero_windows) |}
  | ERR_CONNECTION_RESET =>
      {| err_checksum_failures := stats.(err_checksum_failures);
         err_invalid_segments := stats.(err_invalid_segments);
         err_resets_received := stats.(err_resets_received) + 1;
         err_resets_sent := stats.(err_resets_sent);
         err_retransmit_timeouts := stats.(err_retransmit_timeouts);
         err_zero_windows := stats.(err_zero_windows) |}
  | ERR_CONNECTION_TIMEOUT =>
      {| err_checksum_failures := stats.(err_checksum_failures);
         err_invalid_segments := stats.(err_invalid_segments);
         err_resets_received := stats.(err_resets_received);
         err_resets_sent := stats.(err_resets_sent);
         err_retransmit_timeouts := stats.(err_retransmit_timeouts) + 1;
         err_zero_windows := stats.(err_zero_windows) |}
  | _ => stats
  end.

(* =============================================================================
   Section 25: Updated Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive nat => "int" [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inductive N => "int" [ "0" "(fun p -> p)" ].
Extract Inductive option => "option" [ "None" "Some" ].

Extraction "tcp_complete.ml"
  (* Core functions *)
  tcp_process_segment
  segment_acceptable
  ack_acceptable
  update_window
  generate_ack
  generate_rst
  
  (* User API *)
  handle_user_open_active
  handle_user_open_passive
  handle_user_close
  handle_user_abort
  
  (* Congestion control *)
  slow_start_increase
  congestion_avoidance_increase  
  enter_loss_recovery
  exponential_backoff_rto
  process_ack_in_established
  
  (* Retransmission *)
  add_to_retrans_queue
  remove_acked_from_queue
  handle_retransmit_timeout
  
  (* RTT Measurement *)
  update_rtt_measurement
  
  (* Persist Timer *)
  start_persist_timer
  handle_persist_timeout
  
  (* Nagle's Algorithm *)
  should_send_nagle
  update_nagle_timer
  
  (* SWS Avoidance *)
  should_send_sws
  receiver_sws_check
  
  (* Delayed ACKs *)
  should_send_immediate_ack
  update_delayed_ack
  handle_delack_timeout
  
  (* Keepalive *)
  start_keepalive
  handle_keepalive_timeout
  
  (* Error Handling *)
  validate_segment_checksum
  validate_state_transition
  update_error_stats
  
  (* Simultaneous Open/Close *)
  handle_simultaneous_open
  handle_simultaneous_close
  
  (* Reassembly *)
  reassembly_update
  insert_sorted
  coalesce_sorted
  advance_contiguous
  
  (* Utilities *)
  seq_add
  seq_sub
  seq_lt
  seq_leq
  seq_between
  segment_length
  valid_header
  parse_tcp_options
  calculate_tcp_checksum.
     
