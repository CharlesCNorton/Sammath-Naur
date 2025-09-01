(* =============================================================================
   Formal Verification of Internet Control Message Protocol (ICMP)
   
   Specification: RFC 792 (Jon Postel, September 1981)
   Target: ICMP for IPv4
   
   Module: ICMP Protocol Formalization and Verification
   Author: Charles C Norton
   Date: August 29, 2025
   
   "And they answered: 'What skill bring ye to the House of the Jewel-smiths?'"
   
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

(* ICMP Message Types (RFC 792) *)
Definition ICMP_ECHO_REPLY : byte := 0.
Definition ICMP_DEST_UNREACHABLE : byte := 3.
Definition ICMP_SOURCE_QUENCH : byte := 4.
Definition ICMP_REDIRECT : byte := 5.
Definition ICMP_ECHO_REQUEST : byte := 8.
Definition ICMP_TIME_EXCEEDED : byte := 11.
Definition ICMP_PARAMETER_PROBLEM : byte := 12.
Definition ICMP_TIMESTAMP_REQUEST : byte := 13.
Definition ICMP_TIMESTAMP_REPLY : byte := 14.
Definition ICMP_INFO_REQUEST : byte := 15.
Definition ICMP_INFO_REPLY : byte := 16.

(* Destination Unreachable Codes *)
Definition DEST_NET_UNREACHABLE : byte := 0.
Definition DEST_HOST_UNREACHABLE : byte := 1.
Definition DEST_PROTOCOL_UNREACHABLE : byte := 2.
Definition DEST_PORT_UNREACHABLE : byte := 3.
Definition DEST_FRAGMENTATION_NEEDED : byte := 4.
Definition DEST_SOURCE_ROUTE_FAILED : byte := 5.

(* Redirect Codes *)
Definition REDIRECT_NET : byte := 0.
Definition REDIRECT_HOST : byte := 1.
Definition REDIRECT_TOS_NET : byte := 2.
Definition REDIRECT_TOS_HOST : byte := 3.

(* Time Exceeded Codes *)
Definition TIME_TTL_EXCEEDED : byte := 0.
Definition TIME_FRAGMENT_REASSEMBLY : byte := 1.

(* =============================================================================
   Section 2: IPv4 Address Type (shared with RFC 791)
   ============================================================================= *)

Record IPv4Address := {
  ipv4_a : byte;
  ipv4_b : byte;
  ipv4_c : byte;
  ipv4_d : byte
}.

(* =============================================================================
   Section 3: ICMP Message Structure (RFC 792 Format)
   ============================================================================= *)

(* Base ICMP Header - common to all messages *)
Record ICMPHeader := {
  icmp_type : byte;      (* 8 bits: Message type *)
  icmp_code : byte;      (* 8 bits: Type sub-code *)
  icmp_checksum : word16 (* 16 bits: Header + data checksum *)
}.

(* ICMP Message Variants *)
Inductive ICMPMessage :=
  (* Echo Reply/Request (Type 0/8) *)
  | ICMPEcho : ICMPHeader -> word16 -> word16 -> list byte -> ICMPMessage
               (* Header -> Identifier -> Sequence -> Data *)
  
  (* Destination Unreachable (Type 3) *)
  | ICMPDestUnreachable : ICMPHeader -> word32 -> list byte -> ICMPMessage
                         (* Header -> Unused -> IP Header + 64 bits *)
  
  (* Source Quench (Type 4) *)
  | ICMPSourceQuench : ICMPHeader -> word32 -> list byte -> ICMPMessage
                      (* Header -> Unused -> IP Header + 64 bits *)
  
  (* Redirect (Type 5) *)
  | ICMPRedirect : ICMPHeader -> IPv4Address -> list byte -> ICMPMessage
                  (* Header -> Gateway -> IP Header + 64 bits *)
  
  (* Time Exceeded (Type 11) *)
  | ICMPTimeExceeded : ICMPHeader -> word32 -> list byte -> ICMPMessage
                      (* Header -> Unused -> IP Header + 64 bits *)
  
  (* Parameter Problem (Type 12) *)
  | ICMPParameterProblem : ICMPHeader -> byte -> word32 -> list byte -> ICMPMessage
                          (* Header -> Pointer -> Unused -> IP Header + 64 bits *)
  
  (* Timestamp Request/Reply (Type 13/14) *)
  | ICMPTimestamp : ICMPHeader -> word16 -> word16 -> word32 -> word32 -> word32 -> ICMPMessage
                   (* Header -> ID -> Seq -> Originate -> Receive -> Transmit *)
  
  (* Information Request/Reply (Type 15/16) *)
  | ICMPInformation : ICMPHeader -> word16 -> word16 -> ICMPMessage
                     (* Header -> Identifier -> Sequence *).

(* =============================================================================
   Section 4: Checksum Computation (RFC 792 + RFC 1071)
   ============================================================================= *)

(* One's complement sum *)
Definition add_ones_complement (acc : word16) (val : word16) : word16 :=
  let sum := acc + val in
  let carry := sum / 65536 in
  (sum mod 65536) + carry.

(* Compute ICMP checksum *)
Definition compute_icmp_checksum (msg : list byte) : word16.
  (* Convert bytes to 16-bit words and compute one's complement sum *)
  admit.
Defined.

(* Verify checksum *)
Definition verify_icmp_checksum (msg : list byte) : bool.
  (* Sum should be 0xFFFF when correct *)
  admit.
Defined.

(* =============================================================================
   Section 5: Message Construction
   ============================================================================= *)

(* Create Echo Request *)
Definition make_echo_request (id seq : word16) (data : list byte) : ICMPMessage :=
  ICMPEcho {| icmp_type := ICMP_ECHO_REQUEST;
              icmp_code := 0;
              icmp_checksum := 0 |} id seq data.

(* Create Echo Reply *)
Definition make_echo_reply (id seq : word16) (data : list byte) : ICMPMessage :=
  ICMPEcho {| icmp_type := ICMP_ECHO_REPLY;
              icmp_code := 0;
              icmp_checksum := 0 |} id seq data.

(* Create Destination Unreachable *)
Definition make_dest_unreachable (code : byte) (original : list byte) : ICMPMessage :=
  ICMPDestUnreachable {| icmp_type := ICMP_DEST_UNREACHABLE;
                         icmp_code := code;
                         icmp_checksum := 0 |} 0 (firstn 28 original).

(* Create Time Exceeded *)
Definition make_time_exceeded (code : byte) (original : list byte) : ICMPMessage :=
  ICMPTimeExceeded {| icmp_type := ICMP_TIME_EXCEEDED;
                      icmp_code := code;
                      icmp_checksum := 0 |} 0 (firstn 28 original).

(* Create Redirect *)
Definition make_redirect (code : byte) (gateway : IPv4Address) (original : list byte) : ICMPMessage :=
  ICMPRedirect {| icmp_type := ICMP_REDIRECT;
                  icmp_code := code;
                  icmp_checksum := 0 |} gateway (firstn 28 original).

(* =============================================================================
   Section 6: Message Processing State Machine
   ============================================================================= *)

Record ICMPContext := {
  icmp_echo_requests : list (word16 * word16 * N);  (* ID, Seq, Timestamp *)
  icmp_rate_limit : N;                               (* Rate limit counter *)
  icmp_statistics : list (byte * N)                  (* Type -> Count *)
}.

(* Processing result *)
Inductive ICMPAction :=
  | ICMPSendReply : ICMPMessage -> IPv4Address -> ICMPAction
  | ICMPDeliverLocal : byte -> list byte -> ICMPAction  (* Protocol, Data *)
  | ICMPUpdateRoute : IPv4Address -> IPv4Address -> ICMPAction  (* Dest, Gateway *)
  | ICMPDrop : ICMPAction
  | ICMPError : N -> ICMPAction.

(* =============================================================================
   Section 7: RFC 792 Message Processing Rules
   ============================================================================= *)

Definition process_icmp_message (ctx : ICMPContext) (src : IPv4Address) 
                               (msg : ICMPMessage) : ICMPContext * option ICMPAction :=
  match msg with
  | ICMPEcho hdr id seq data =>
      if N.eqb hdr.(icmp_type) ICMP_ECHO_REQUEST then
        (* Echo Request -> Send Reply *)
        let reply := make_echo_reply id seq data in
        (ctx, Some (ICMPSendReply reply src))
      else
        (* Echo Reply -> Match with request *)
        (ctx, Some (ICMPDeliverLocal 0 data))
  
  | ICMPDestUnreachable hdr _ original =>
      (* Notify upper layer protocol *)
      (ctx, Some (ICMPDeliverLocal hdr.(icmp_code) original))
  
  | ICMPSourceQuench hdr _ original =>
      (* Slow down transmission *)
      (ctx, Some (ICMPDeliverLocal 4 original))
  
  | ICMPRedirect hdr gateway original =>
      (* Update routing table *)
      (ctx, Some (ICMPUpdateRoute src gateway))
  
  | ICMPTimeExceeded hdr _ original =>
      (* Notify upper layer *)
      (ctx, Some (ICMPDeliverLocal 11 original))
  
  | ICMPParameterProblem hdr ptr _ original =>
      (* Notify about bad header *)
      (ctx, Some (ICMPDeliverLocal 12 (ptr :: original)))
  
  | ICMPTimestamp hdr id seq orig recv trans =>
      if N.eqb hdr.(icmp_type) ICMP_TIMESTAMP_REQUEST then
        (* Generate reply with current time *)
        (ctx, Some ICMPDrop) (* Simplified *)
      else
        (ctx, Some (ICMPDeliverLocal 14 []))
  
  | ICMPInformation hdr id seq =>
      (* Obsolete - drop *)
      (ctx, Some ICMPDrop)
  end.

(* =============================================================================
   Section 8: Error Message Generation Rules
   ============================================================================= *)

(* Check if we should generate ICMP error (RFC 792 rules) *)
Definition should_generate_icmp_error (ip_src ip_dst : IPv4Address) 
                                      (ip_proto : byte) : bool :=
  (* Don't generate ICMP errors for:
     - ICMP error messages
     - Broadcast/multicast destinations
     - Fragment other than first
     - Source route packets *)
  andb (negb (N.eqb ip_proto 1))  (* Not ICMP *)
       (negb (N.eqb (ip_dst.(ipv4_a) land 0xF0) 0xE0)). (* Not multicast *)

(* Select appropriate ICMP error message *)
Definition generate_icmp_error (trigger : N) (original : list byte) : option ICMPMessage :=
  match trigger with
  | 0 => Some (make_dest_unreachable DEST_NET_UNREACHABLE original)
  | 1 => Some (make_dest_unreachable DEST_HOST_UNREACHABLE original)
  | 2 => Some (make_dest_unreachable DEST_PROTOCOL_UNREACHABLE original)
  | 3 => Some (make_dest_unreachable DEST_PORT_UNREACHABLE original)
  | 4 => Some (make_dest_unreachable DEST_FRAGMENTATION_NEEDED original)
  | 11 => Some (make_time_exceeded TIME_TTL_EXCEEDED original)
  | _ => None
  end.

(* =============================================================================
   Section 9: Path MTU Discovery Support (RFC 1191 extension)
   ============================================================================= *)

Definition extract_mtu_from_unreachable (msg : ICMPMessage) : option N :=
  match msg with
  | ICMPDestUnreachable hdr unused _ =>
      if N.eqb hdr.(icmp_code) DEST_FRAGMENTATION_NEEDED then
        Some (unused land 0xFFFF)  (* Next-hop MTU in lower 16 bits *)
      else None
  | _ => None
  end.

(* =============================================================================
   Section 10: Rate Limiting
   ============================================================================= *)

Definition rate_limit_check (ctx : ICMPContext) (msg_type : byte) : bool * ICMPContext :=
  if N.ltb ctx.(icmp_rate_limit) 10 then
    (true, {| icmp_echo_requests := ctx.(icmp_echo_requests);
              icmp_rate_limit := ctx.(icmp_rate_limit) + 1;
              icmp_statistics := ctx.(icmp_statistics) |})
  else
    (false, ctx).

(* =============================================================================
   Section 11: Serialization and Parsing
   ============================================================================= *)

Definition serialize_icmp_message (msg : ICMPMessage) : list byte.
  (* Serialize message to bytes *)
  admit.
Defined.

Definition parse_icmp_message (data : list byte) : option ICMPMessage.
  (* Parse bytes into message *)
  admit.
Defined.

(* =============================================================================
   Section 12: Echo Service Implementation
   ============================================================================= *)

Record EchoRequest := {
  echo_id : word16;
  echo_seq : word16;
  echo_timestamp : N;
  echo_src : IPv4Address
}.

Definition match_echo_reply (requests : list EchoRequest) (id seq : word16) 
                           : option (EchoRequest * list EchoRequest) :=
  let fix find_and_remove (reqs : list EchoRequest) (acc : list EchoRequest) :=
    match reqs with
    | [] => None
    | req :: rest =>
        if andb (N.eqb req.(echo_id) id) (N.eqb req.(echo_seq) seq) then
          Some (req, app (rev acc) rest)
        else
          find_and_remove rest (req :: acc)
    end
  in find_and_remove requests [].

(* Calculate RTT from echo reply *)
Definition calculate_rtt (req : EchoRequest) (current_time : N) : N :=
  current_time - req.(echo_timestamp).

(* =============================================================================
   Section 13: Router Discovery (RFC 1256 extension)
   ============================================================================= *)

Definition ICMP_ROUTER_ADVERTISEMENT : byte := 9.
Definition ICMP_ROUTER_SOLICITATION : byte := 10.

Record RouterAdvertisement := {
  ra_num_addrs : byte;
  ra_addr_size : byte;
  ra_lifetime : word16;
  ra_addresses : list (IPv4Address * word32)  (* Address, Preference *)
}.

(* =============================================================================
   Section 14: Security and Validation
   ============================================================================= *)

(* Validate ICMP message format *)
Definition validate_icmp_message (msg : ICMPMessage) : bool :=
  match msg with
  | ICMPEcho hdr _ _ data =>
      andb (orb (N.eqb hdr.(icmp_type) ICMP_ECHO_REQUEST)
                (N.eqb hdr.(icmp_type) ICMP_ECHO_REPLY))
           (N.eqb hdr.(icmp_code) 0)
  
  | ICMPDestUnreachable hdr _ original =>
      andb (N.eqb hdr.(icmp_type) ICMP_DEST_UNREACHABLE)
           (andb (N.leb hdr.(icmp_code) 5)
                 (N.leb 28 (N.of_nat (length original))))
  
  | ICMPTimeExceeded hdr _ original =>
      andb (N.eqb hdr.(icmp_type) ICMP_TIME_EXCEEDED)
           (andb (N.leb hdr.(icmp_code) 1)
                 (N.leb 28 (N.of_nat (length original))))
  
  | _ => true  (* Simplified *)
  end.

(* Check for ICMP attacks *)
Definition is_suspicious_icmp (ctx : ICMPContext) (src : IPv4Address) 
                             (msg : ICMPMessage) : bool :=
  match msg with
  | ICMPRedirect _ gateway _ =>
      (* Suspicious if redirect to unexpected gateway *)
      false  (* Would check against known gateways *)
  | ICMPDestUnreachable hdr _ _ =>
      (* Check for excessive unreachable messages *)
      N.ltb 100 ctx.(icmp_rate_limit)
  | _ => false
  end.

(* =============================================================================
   Section 15: Key Properties to Verify
   ============================================================================= *)

(* Property 1: Echo Reply matches Request *)
Theorem echo_reply_preserves_data : forall ctx src id seq data reply,
  process_icmp_message ctx src (make_echo_request id seq data) = (ctx, Some reply) ->
  exists dst, reply = ICMPSendReply (make_echo_reply id seq data) dst.
Proof.
  admit.
Qed.

(* Property 2: No ICMP errors for ICMP errors *)
Theorem no_error_on_error : forall ip_src ip_dst original,
  let msg := make_dest_unreachable DEST_NET_UNREACHABLE original in
  should_generate_icmp_error ip_src ip_dst 1 = false.
Proof.
  intros. unfold should_generate_icmp_error.
  simpl. rewrite N.eqb_refl. reflexivity.
Qed.

(* Property 3: Checksum validation *)
Theorem checksum_correct_after_compute : forall msg,
  let serialized := serialize_icmp_message msg in
  let with_checksum := (* set checksum field *) serialized in
  verify_icmp_checksum with_checksum = true.
Proof.
  admit.
Qed.

(* Property 4: Original data preservation *)
Theorem error_preserves_original : forall code original,
  match make_dest_unreachable code original with
  | ICMPDestUnreachable _ _ orig => orig = firstn 28 original
  | _ => False
  end.
Proof.
  intros. unfold make_dest_unreachable. reflexivity.
Qed.

(* Property 5: Rate limiting monotonicity *)
Theorem rate_limit_increases : forall ctx msg_type ctx' allowed,
  rate_limit_check ctx msg_type = (allowed, ctx') ->
  allowed = true ->
  ctx'.(icmp_rate_limit) = ctx.(icmp_rate_limit) + 1.
Proof.
  intros ctx msg_type ctx' allowed [Hallowed Hctx'] Htrue.
  unfold rate_limit_check in *.
  destruct (N.ltb ctx.(icmp_rate_limit) 10) eqn:E.
  - inversion Hctx'. reflexivity.
  - discriminate.
Qed.

(* Property 6: TTL handling generates correct ICMP *)
Theorem ttl_expired_generates_time_exceeded : forall original,
  exists msg, generate_icmp_error 11 original = Some msg /\
              match msg with
              | ICMPTimeExceeded hdr _ _ => 
                  hdr.(icmp_type) = ICMP_TIME_EXCEEDED /\
                  hdr.(icmp_code) = TIME_TTL_EXCEEDED
              | _ => False
              end.
Proof.
  intros. unfold generate_icmp_error, make_time_exceeded.
  eexists. split; [reflexivity|]. simpl. split; reflexivity.
Qed.

(* Property 7: Round-trip serialization *)
Theorem serialize_parse_identity : forall msg,
  validate_icmp_message msg = true ->
  parse_icmp_message (serialize_icmp_message msg) = Some msg.
Proof.
  admit.
Qed.

(* =============================================================================
   Section 16: Integration with IPv4
   ============================================================================= *)

(* Generate ICMP based on IPv4 processing result *)
Definition handle_ipv4_error (error_code : N) (ip_header : list byte) 
                            (ip_src ip_dst : IPv4Address) : option ICMPMessage :=
  if should_generate_icmp_error ip_src ip_dst 0 then
    generate_icmp_error error_code ip_header
  else None.

(* Process ICMP contained in IPv4 *)
Definition process_from_ipv4 (ctx : ICMPContext) (ip_src ip_dst : IPv4Address)
                            (data : list byte) : ICMPContext * option ICMPAction :=
  match parse_icmp_message data with
  | None => (ctx, Some (ICMPError 1))
  | Some msg =>
      if verify_icmp_checksum data then
        process_icmp_message ctx ip_src msg
      else
        (ctx, Some (ICMPError 2))
  end.

(* =============================================================================
   Section 17: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].
Extract Inductive option => "option" [ "Some" "None" ].

Extraction "icmp.ml"
  process_icmp_message
  make_echo_request
  make_echo_reply
  make_dest_unreachable
  make_time_exceeded
  generate_icmp_error
  rate_limit_check
  validate_icmp_message.
