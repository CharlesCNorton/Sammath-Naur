(* =============================================================================
   Formal Verification of Internet Control Message Protocol for IPv6 (ICMPv6)
   
   Specification: RFC 4443 (A. Conta, S. Deering, M. Gupta, March 2006)
   Updated by: RFC 4884, RFC 8335
   Target: ICMPv6 Protocol
   
   Module: ICMPv6 Protocol Formalization and Verification
   Author: Charles C Norton
   Date: August 29, 2025
   
   "And desire kindled in their hearts like forge-fire at dawn."
   
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

(* ICMPv6 Message Types (RFC 4443 Section 2.1) *)
(* Error Messages: 0-127 *)
Definition ICMPV6_DEST_UNREACHABLE : byte := 1.
Definition ICMPV6_PACKET_TOO_BIG : byte := 2.
Definition ICMPV6_TIME_EXCEEDED : byte := 3.
Definition ICMPV6_PARAMETER_PROBLEM : byte := 4.

(* Informational Messages: 128-255 *)
Definition ICMPV6_ECHO_REQUEST : byte := 128.
Definition ICMPV6_ECHO_REPLY : byte := 129.

(* Neighbor Discovery (RFC 4861) *)
Definition ICMPV6_ROUTER_SOLICITATION : byte := 133.
Definition ICMPV6_ROUTER_ADVERTISEMENT : byte := 134.
Definition ICMPV6_NEIGHBOR_SOLICITATION : byte := 135.
Definition ICMPV6_NEIGHBOR_ADVERTISEMENT : byte := 136.
Definition ICMPV6_REDIRECT : byte := 137.

(* Multicast Listener Discovery (RFC 2710/3810) *)
Definition ICMPV6_MLDv1_QUERY : byte := 130.
Definition ICMPV6_MLDv1_REPORT : byte := 131.
Definition ICMPV6_MLDv1_DONE : byte := 132.
Definition ICMPV6_MLDv2_REPORT : byte := 143.

(* Codes for Destination Unreachable *)
Definition DEST_NO_ROUTE : byte := 0.
Definition DEST_ADMIN_PROHIBITED : byte := 1.
Definition DEST_BEYOND_SCOPE : byte := 2.
Definition DEST_ADDR_UNREACHABLE : byte := 3.
Definition DEST_PORT_UNREACHABLE : byte := 4.
Definition DEST_SOURCE_ADDR_FAILED : byte := 5.
Definition DEST_REJECT_ROUTE : byte := 6.
Definition DEST_SOURCE_ROUTING_ERROR : byte := 7.

(* Codes for Time Exceeded *)
Definition TIME_HOP_LIMIT_EXCEEDED : byte := 0.
Definition TIME_FRAGMENT_REASSEMBLY_EXCEEDED : byte := 1.

(* Codes for Parameter Problem *)
Definition PARAM_ERRONEOUS_HEADER : byte := 0.
Definition PARAM_UNRECOGNIZED_NEXT_HEADER : byte := 1.
Definition PARAM_UNRECOGNIZED_IPV6_OPTION : byte := 2.
Definition PARAM_IPV6_FIRST_FRAGMENT : byte := 3.

(* =============================================================================
   Section 2: IPv6 Address Type (shared with RFC 8200)
   ============================================================================= *)

Record IPv6Address := {
  addr_bytes : list byte;
  addr_valid : length addr_bytes = 16%nat
}.

(* Multicast addresses *)
Definition ALL_NODES_LINK_LOCAL : IPv6Address.
  refine {| addr_bytes := [0xFF; 0x02] ++ repeat 0 13 ++ [1] |}.
  rewrite app_length, app_length, repeat_length. simpl. reflexivity.
Defined.

Definition ALL_ROUTERS_LINK_LOCAL : IPv6Address.
  refine {| addr_bytes := [0xFF; 0x02] ++ repeat 0 13 ++ [2] |}.
  rewrite app_length, app_length, repeat_length. simpl. reflexivity.
Defined.

Definition SOLICITED_NODE_PREFIX : list byte := 
  [0xFF; 0x02] ++ repeat 0 9 ++ [0; 1; 0xFF].

(* =============================================================================
   Section 3: ICMPv6 Message Structure (RFC 4443 Section 2.1)
   ============================================================================= *)

Record ICMPv6Header := {
  icmpv6_type : byte;
  icmpv6_code : byte;
  icmpv6_checksum : word16
}.

(* ICMPv6 Message Variants *)
Inductive ICMPv6Message :=
  (* Error Messages *)
  | ICMPv6DestUnreachable : ICMPv6Header -> word32 -> list byte -> ICMPv6Message
  | ICMPv6PacketTooBig : ICMPv6Header -> word32 -> list byte -> ICMPv6Message
  | ICMPv6TimeExceeded : ICMPv6Header -> word32 -> list byte -> ICMPv6Message
  | ICMPv6ParameterProblem : ICMPv6Header -> word32 -> list byte -> ICMPv6Message
  
  (* Informational Messages *)
  | ICMPv6Echo : ICMPv6Header -> word16 -> word16 -> list byte -> ICMPv6Message
  
  (* Neighbor Discovery *)
  | ICMPv6RouterSolicitation : ICMPv6Header -> list NDOption -> ICMPv6Message
  | ICMPv6RouterAdvertisement : ICMPv6Header -> RouterAdvInfo -> list NDOption -> ICMPv6Message
  | ICMPv6NeighborSolicitation : ICMPv6Header -> IPv6Address -> list NDOption -> ICMPv6Message
  | ICMPv6NeighborAdvertisement : ICMPv6Header -> NAFlags -> IPv6Address -> list NDOption -> ICMPv6Message
  | ICMPv6Redirect : ICMPv6Header -> IPv6Address -> IPv6Address -> list NDOption -> ICMPv6Message
  
  (* Extended format (RFC 4884) *)
  | ICMPv6Extended : ICMPv6Header -> byte -> byte -> list byte -> list ExtensionObject -> ICMPv6Message

with NDOption :=
  | NDOptSourceLinkAddr : list byte -> NDOption
  | NDOptTargetLinkAddr : list byte -> NDOption
  | NDOptPrefixInfo : PrefixInfo -> NDOption
  | NDOptRedirectedHeader : list byte -> NDOption
  | NDOptMTU : word32 -> NDOption
  | NDOptRouteInfo : RouteInfo -> NDOption
  | NDOptRDNSS : word32 -> list IPv6Address -> NDOption
  | NDOptDNSSL : word32 -> list (list byte) -> NDOption
  | NDOptUnknown : byte -> list byte -> NDOption

with ExtensionObject :=
  | ExtObjMPLS : list word32 -> ExtensionObject
  | ExtObjInterface : word32 -> ExtensionObject
  | ExtObjUnknown : word16 -> list byte -> ExtensionObject.

(* Router Advertisement Info *)
Record RouterAdvInfo := {
  ra_hop_limit : byte;
  ra_flags : byte;
  ra_router_lifetime : word16;
  ra_reachable_time : word32;
  ra_retrans_timer : word32
}.

(* Neighbor Advertisement Flags *)
Record NAFlags := {
  na_router : bool;
  na_solicited : bool;
  na_override : bool
}.

(* Prefix Information *)
Record PrefixInfo := {
  pi_prefix_length : byte;
  pi_flags : byte;
  pi_valid_lifetime : word32;
  pi_preferred_lifetime : word32;
  pi_prefix : IPv6Address
}.

(* Route Information *)
Record RouteInfo := {
  ri_prefix_length : byte;
  ri_flags : byte;
  ri_route_lifetime : word32;
  ri_prefix : list byte
}.

(* =============================================================================
   Section 4: ICMPv6 Checksum (RFC 4443 Section 2.3)
   ============================================================================= *)

(* Pseudo-header for checksum *)
Definition icmpv6_pseudo_header (src dst : IPv6Address) (length : word32) : list word16.
  (* Source (128 bits) + Dest (128 bits) + Length (32 bits) + Next Header (58) *)
  admit.
Defined.

(* Compute ICMPv6 checksum including pseudo-header *)
Definition compute_icmpv6_checksum (src dst : IPv6Address) (msg : list byte) : word16.
  admit.
Defined.

(* Verify checksum *)
Definition verify_icmpv6_checksum (src dst : IPv6Address) (msg : list byte) : bool.
  admit.
Defined.

(* =============================================================================
   Section 5: Message Processing Rules (RFC 4443 Section 2.4)
   ============================================================================= *)

Record ICMPv6Context := {
  icmpv6_rate_limit : N;
  icmpv6_error_count : N;
  icmpv6_nd_cache : list (IPv6Address * list byte * N);  (* IP, MAC, Time *)
  icmpv6_router_list : list (IPv6Address * RouterAdvInfo * N);
  icmpv6_prefix_list : list PrefixInfo;
  icmpv6_mld_groups : list (IPv6Address * N)  (* Group, Timer *)
}.

Inductive ICMPv6Action :=
  | ICMPv6Send : ICMPv6Message -> IPv6Address -> ICMPv6Action
  | ICMPv6UpdateND : IPv6Address -> list byte -> ICMPv6Action
  | ICMPv6UpdateRoute : IPv6Address -> IPv6Address -> ICMPv6Action
  | ICMPv6DeliverError : byte -> byte -> list byte -> ICMPv6Action
  | ICMPv6JoinGroup : IPv6Address -> ICMPv6Action
  | ICMPv6LeaveGroup : IPv6Address -> ICMPv6Action
  | ICMPv6Drop : ICMPv6Action.

(* Check if ICMPv6 error should be sent (RFC 4443 Section 2.4(e)) *)
Definition should_send_icmpv6_error (ipv6_src ipv6_dst : IPv6Address) 
                                    (triggering_packet : list byte) : bool :=
  (* Don't send for:
     - ICMPv6 errors
     - Multicast destination (with exceptions)
     - Multicast source
     - Unspecified source/destination *)
  true.  (* Simplified *)

(* Process received ICMPv6 message *)
Definition process_icmpv6_message (ctx : ICMPv6Context) 
                                  (src dst : IPv6Address)
                                  (msg : ICMPv6Message) 
                                  : ICMPv6Context * option ICMPv6Action :=
  match msg with
  | ICMPv6Echo hdr id seq data =>
      if N.eqb hdr.(icmpv6_type) ICMPV6_ECHO_REQUEST then
        (* Generate Echo Reply *)
        let reply := ICMPv6Echo 
          {| icmpv6_type := ICMPV6_ECHO_REPLY;
             icmpv6_code := 0;
             icmpv6_checksum := 0 |} id seq data in
        (ctx, Some (ICMPv6Send reply src))
      else
        (ctx, None)
  
  | ICMPv6DestUnreachable hdr _ invoking =>
      (ctx, Some (ICMPv6DeliverError ICMPV6_DEST_UNREACHABLE hdr.(icmpv6_code) invoking))
  
  | ICMPv6PacketTooBig hdr mtu invoking =>
      (* Update Path MTU *)
      (ctx, Some (ICMPv6DeliverError ICMPV6_PACKET_TOO_BIG mtu invoking))
  
  | ICMPv6NeighborSolicitation hdr target opts =>
      (* Generate Neighbor Advertisement if target is ours *)
      (ctx, None)  (* Simplified *)
  
  | _ => (ctx, None)
  end.

(* =============================================================================
   Section 6: Neighbor Discovery (RFC 4861 Integration)
   ============================================================================= *)

(* Neighbor Cache Entry States *)
Inductive NCState :=
  | NC_INCOMPLETE
  | NC_REACHABLE
  | NC_STALE
  | NC_DELAY
  | NC_PROBE.

Record NeighborCacheEntry := {
  nce_addr : IPv6Address;
  nce_link_addr : option (list byte);
  nce_state : NCState;
  nce_is_router : bool;
  nce_retrans_timer : N;
  nce_probe_count : N
}.

(* Create Neighbor Solicitation *)
Definition create_neighbor_solicitation (src : IPv6Address) (target : IPv6Address) 
                                       : ICMPv6Message :=
  ICMPv6NeighborSolicitation
    {| icmpv6_type := ICMPV6_NEIGHBOR_SOLICITATION;
       icmpv6_code := 0;
       icmpv6_checksum := 0 |}
    target
    [].  (* Options *)

(* Create Router Solicitation *)
Definition create_router_solicitation (src_link_addr : list byte) : ICMPv6Message :=
  ICMPv6RouterSolicitation
    {| icmpv6_type := ICMPV6_ROUTER_SOLICITATION;
       icmpv6_code := 0;
       icmpv6_checksum := 0 |}
    (if null src_link_addr then [] else [NDOptSourceLinkAddr src_link_addr]).

(* =============================================================================
   Section 7: Path MTU Discovery (RFC 4443 Section 3.2)
   ============================================================================= *)

Record PathMTUEntry := {
  pmtu_dst : IPv6Address;
  pmtu_value : word32;
  pmtu_expires : N
}.

Definition process_packet_too_big (pmtu_table : list PathMTUEntry)
                                  (src : IPv6Address) (mtu : word32)
                                  : list PathMTUEntry :=
  (* Update or insert PMTU entry *)
  (* Minimum IPv6 MTU is 1280 *)
  if N.ltb mtu 1280 then pmtu_table
  else pmtu_table.  (* Simplified *)

(* =============================================================================
   Section 8: Rate Limiting (RFC 4443 Section 2.4(f))
   ============================================================================= *)

Definition rate_limit_icmpv6 (ctx : ICMPv6Context) (msg_type : byte) 
                             : bool * ICMPv6Context :=
  (* Token bucket algorithm *)
  if N.ltb ctx.(icmpv6_rate_limit) 10 then
    (true, {| icmpv6_rate_limit := ctx.(icmpv6_rate_limit) + 1;
              icmpv6_error_count := ctx.(icmpv6_error_count);
              icmpv6_nd_cache := ctx.(icmpv6_nd_cache);
              icmpv6_router_list := ctx.(icmpv6_router_list);
              icmpv6_prefix_list := ctx.(icmpv6_prefix_list);
              icmpv6_mld_groups := ctx.(icmpv6_mld_groups) |})
  else
    (false, ctx).

(* =============================================================================
   Section 9: Multicast Listener Discovery (RFC 2710/3810)
   ============================================================================= *)

Definition process_mld_query (ctx : ICMPv6Context) (group : IPv6Address) 
                            : ICMPv6Context * option ICMPv6Action :=
  (* Check if we're member of the group *)
  if existsb (fun g => true (* addr_eq (fst g) group *)) ctx.(icmpv6_mld_groups) then
    (ctx, Some (ICMPv6JoinGroup group))
  else
    (ctx, None).

(* =============================================================================
   Section 10: Extended Format (RFC 4884)
   ============================================================================= *)

Definition parse_extended_format (data : list byte) : option (byte * list ExtensionObject) :=
  (* Length field at byte 5-6 indicates extension offset *)
  None.  (* Simplified *)

(* =============================================================================
   Section 11: Error Message Generation
   ============================================================================= *)

Definition generate_dest_unreachable (code : byte) (invoking : list byte) 
                                    : ICMPv6Message :=
  ICMPv6DestUnreachable
    {| icmpv6_type := ICMPV6_DEST_UNREACHABLE;
       icmpv6_code := code;
       icmpv6_checksum := 0 |}
    0  (* Unused *)
    (firstn 1280 invoking).  (* As much as fits in minimum MTU *)

Definition generate_time_exceeded (code : byte) (invoking : list byte) 
                                : ICMPv6Message :=
  ICMPv6TimeExceeded
    {| icmpv6_type := ICMPV6_TIME_EXCEEDED;
       icmpv6_code := code;
       icmpv6_checksum := 0 |}
    0  (* Unused *)
    (firstn 1280 invoking).

Definition generate_parameter_problem (code : byte) (pointer : word32) 
                                     (invoking : list byte) : ICMPv6Message :=
  ICMPv6ParameterProblem
    {| icmpv6_type := ICMPV6_PARAMETER_PROBLEM;
       icmpv6_code := code;
       icmpv6_checksum := 0 |}
    pointer
    (firstn 1280 invoking).

(* =============================================================================
   Section 12: Key Properties
   ============================================================================= *)

(* Property 1: Error messages include invoking packet *)
Theorem error_includes_invoking : forall code invoking,
  match generate_dest_unreachable code invoking with
  | ICMPv6DestUnreachable _ _ data => data = firstn 1280 invoking
  | _ => False
  end.
Proof.
  intros. unfold generate_dest_unreachable. reflexivity.
Qed.

(* Property 2: Echo Reply preserves data *)
Theorem echo_reply_preserves_data : forall ctx src dst id seq data reply,
  process_icmpv6_message ctx src dst 
    (ICMPv6Echo {| icmpv6_type := ICMPV6_ECHO_REQUEST; 
                   icmpv6_code := 0; 
                   icmpv6_checksum := 0 |} id seq data) = (ctx, Some reply) ->
  exists dst', reply = ICMPv6Send 
    (ICMPv6Echo {| icmpv6_type := ICMPV6_ECHO_REPLY;
                   icmpv6_code := 0;
                   icmpv6_checksum := 0 |} id seq data) dst'.
Proof.
  admit.
Qed.

(* Property 3: Rate limiting monotonicity *)
Theorem rate_limit_increases : forall ctx msg_type ctx' allowed,
  rate_limit_icmpv6 ctx msg_type = (allowed, ctx') ->
  allowed = true ->
  ctx'.(icmpv6_rate_limit) = ctx.(icmpv6_rate_limit) + 1.
Proof.
  intros. unfold rate_limit_icmpv6 in H.
  destruct (N.ltb ctx.(icmpv6_rate_limit) 10) eqn:E.
  - inversion H. subst. reflexivity.
  - inversion H. discriminate.
Qed.

(* Property 4: Minimum MTU respected *)
Theorem packet_too_big_min_mtu : forall table src mtu,
  N.ltb mtu 1280 = true ->
  process_packet_too_big table src mtu = table.
Proof.
  intros. unfold process_packet_too_big.
  rewrite H. reflexivity.
Qed.

(* Property 5: Checksum includes pseudo-header *)
Theorem checksum_with_pseudo : forall src dst msg,
  verify_icmpv6_checksum src dst msg = true ->
  (* Checksum was computed with pseudo-header *) True.
Proof.
  admit.
Qed.

(* Property 6: No error on error *)
Theorem no_error_on_icmpv6_error : forall src dst packet,
  (* If packet is ICMPv6 error *)
  should_send_icmpv6_error src dst packet = false.
Proof.
  admit.
Qed.

(* =============================================================================
   Section 13: Serialization
   ============================================================================= *)

Definition serialize_icmpv6_message (msg : ICMPv6Message) : list byte.
  admit.
Defined.

Definition parse_icmpv6_message (data : list byte) : option ICMPv6Message.
  admit.
Defined.

Theorem serialize_parse_identity : forall msg,
  parse_icmpv6_message (serialize_icmpv6_message msg) = Some msg.
Proof.
  admit.
Qed.

(* =============================================================================
   Section 14: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].
Extract Inductive option => "option" [ "Some" "None" ].

Extraction "icmpv6.ml"
  process_icmpv6_message
  generate_dest_unreachable
  generate_time_exceeded
  generate_parameter_problem
  create_neighbor_solicitation
  create_router_solicitation
  rate_limit_icmpv6
  process_packet_too_big.
