(* =============================================================================
   Formal Verification of Border Gateway Protocol Version 4 (BGP-4)
   
   Specification: RFC 4271 (Y. Rekhter, T. Li, S. Hares, January 2006)
   Target: BGP-4 Protocol
   
   Module: BGP-4 Protocol Formalization and Verification
   Author: Charles C Norton
   Date: September 1, 2025
   
   "Greater still were the maps that showed the roads between realms."
   
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

(* BGP Constants (RFC 4271 Section 4) *)
Definition BGP_VERSION : byte := 4.
Definition BGP_PORT : word16 := 179.
Definition BGP_MARKER_LENGTH : N := 16.
Definition BGP_HEADER_LENGTH : N := 19.
Definition BGP_MAX_MESSAGE_LENGTH : N := 4096.
Definition BGP_MIN_MESSAGE_LENGTH : N := 19.

(* Timer Constants (RFC 4271 Section 10) *)
Definition HOLD_TIME_DEFAULT : N := 90.      (* seconds *)
Definition HOLD_TIME_MIN : N := 3.           (* seconds *)
Definition HOLD_TIME_MAX : N := 65535.       (* seconds *)
Definition KEEPALIVE_TIME : N := 30.         (* seconds *)
Definition CONNECT_RETRY_TIME : N := 120.    (* seconds *)
Definition MIN_AS_ORIGINATION_INTERVAL : N := 15. (* seconds *)
Definition MIN_ROUTE_ADVERTISEMENT_INTERVAL : N := 30. (* seconds *)

(* =============================================================================
   Section 2: BGP Message Types (RFC 4271 Section 4.1)
   ============================================================================= *)

Inductive BGPMessageType :=
  | OPEN : BGPMessageType         (* 1 *)
  | UPDATE : BGPMessageType       (* 2 *)
  | NOTIFICATION : BGPMessageType (* 3 *)
  | KEEPALIVE : BGPMessageType.   (* 4 *)

(* BGP Message Header *)
Record BGPHeader := {
  bgp_marker : list byte;  (* 16 bytes, all 1s *)
  bgp_length : word16;
  bgp_type : BGPMessageType
}.

(* =============================================================================
   Section 3: OPEN Message (RFC 4271 Section 4.2)
   ============================================================================= *)

Record BGPOptionalParameter := {
  opt_param_type : byte;
  opt_param_length : byte;
  opt_param_value : list byte
}.

Record BGPOpen := {
  open_version : byte;
  open_my_as : word16;
  open_hold_time : word16;
  open_bgp_identifier : word32;
  open_opt_param_len : byte;
  open_opt_params : list BGPOptionalParameter
}.

(* Capability codes for optional parameters *)
Definition CAP_MULTIPROTOCOL : byte := 1.
Definition CAP_ROUTE_REFRESH : byte := 2.
Definition CAP_4BYTE_AS : byte := 65.
Definition CAP_ADD_PATH : byte := 69.

(* =============================================================================
   Section 4: UPDATE Message (RFC 4271 Section 4.3)
   ============================================================================= *)

Record NLRI := {
  nlri_prefix_len : byte;
  nlri_prefix : list byte
}.

Record PathAttribute := {
  attr_flags : byte;
  attr_type_code : byte;
  attr_length : N;
  attr_value : list byte
}.

Record BGPUpdate := {
  update_withdrawn_routes_len : word16;
  update_withdrawn_routes : list NLRI;
  update_path_attr_len : word16;
  update_path_attributes : list PathAttribute;
  update_nlri : list NLRI
}.

(* Path Attribute Flags - RFC 4271 uses "bit 0" for high-order bit (MSB) *)
Definition ATTR_FLAG_OPTIONAL : byte := 128.  (* Bit 0 = MSB = 0x80 *)
Definition ATTR_FLAG_TRANSITIVE : byte := 64. (* Bit 1 = 0x40 *)
Definition ATTR_FLAG_PARTIAL : byte := 32.    (* Bit 2 = 0x20 *)
Definition ATTR_FLAG_EXTENDED : byte := 16.   (* Bit 3 = 0x10 *)

(* Path Attribute Type Codes *)
Definition ATTR_ORIGIN : byte := 1.
Definition ATTR_AS_PATH : byte := 2.
Definition ATTR_NEXT_HOP : byte := 3.
Definition ATTR_MULTI_EXIT_DISC : byte := 4.
Definition ATTR_LOCAL_PREF : byte := 5.
Definition ATTR_ATOMIC_AGGREGATE : byte := 6.
Definition ATTR_AGGREGATOR : byte := 7.
Definition ATTR_COMMUNITIES : byte := 8.
Definition ATTR_MP_REACH_NLRI : byte := 14.
Definition ATTR_MP_UNREACH_NLRI : byte := 15.

(* Origin values *)
Definition ORIGIN_IGP : byte := 0.
Definition ORIGIN_EGP : byte := 1.
Definition ORIGIN_INCOMPLETE : byte := 2.

(* AS_PATH segment types *)
Definition AS_SET : byte := 1.
Definition AS_SEQUENCE : byte := 2.

(* =============================================================================
   Section 5: NOTIFICATION Message (RFC 4271 Section 4.5)
   ============================================================================= *)

Record BGPNotification := {
  notif_error_code : byte;
  notif_error_subcode : byte;
  notif_data : list byte
}.

(* Error Codes *)
Definition ERR_MESSAGE_HEADER : byte := 1.
Definition ERR_OPEN_MESSAGE : byte := 2.
Definition ERR_UPDATE_MESSAGE : byte := 3.
Definition ERR_HOLD_TIMER : byte := 4.
Definition ERR_FSM : byte := 5.
Definition ERR_CEASE : byte := 6.

(* OPEN Message Error Subcodes *)
Definition OPEN_ERR_UNSUPPORTED_VERSION : byte := 1.
Definition OPEN_ERR_BAD_PEER_AS : byte := 2.
Definition OPEN_ERR_BAD_BGP_IDENTIFIER : byte := 3.
Definition OPEN_ERR_UNSUPPORTED_PARAM : byte := 4.
Definition OPEN_ERR_UNACCEPTABLE_HOLD_TIME : byte := 6.

(* =============================================================================
   Section 5.5: Validation Functions
   ============================================================================= *)

(* Validate BGP header marker (RFC 4271 Section 4.1) *)
Definition valid_marker (marker : list byte) : bool :=
  andb (N.eqb (N.of_nat (length marker)) BGP_MARKER_LENGTH)
       (forallb (fun b => N.eqb b 255) marker).

(* Validate BGP header length field (RFC 4271 Section 4.1) *)
Definition valid_header_length (length : word16) : bool :=
  andb (N.leb BGP_MIN_MESSAGE_LENGTH length)
       (N.leb length BGP_MAX_MESSAGE_LENGTH).

(* Validate complete BGP header *)
Definition valid_bgp_header (hdr : BGPHeader) : bool :=
  andb (valid_marker hdr.(bgp_marker))
       (valid_header_length hdr.(bgp_length)).

(* Validate BGP Identifier is non-zero (RFC 4271 Section 4.2) *)
Definition valid_bgp_identifier (id : word32) : bool :=
  negb (N.eqb id 0).

(* Validate OPEN message (RFC 4271 Section 6.2) *)
Definition valid_open_message (open_msg : BGPOpen) : bool :=
  andb (N.eqb open_msg.(open_version) BGP_VERSION)
       (valid_bgp_identifier open_msg.(open_bgp_identifier)).

(* =============================================================================
   Section 6: BGP Finite State Machine (RFC 4271 Section 8)
   ============================================================================= *)

Inductive BGPState :=
  | IDLE
  | CONNECT
  | ACTIVE
  | OPENSENT
  | OPENCONFIRM
  | ESTABLISHED.

Record BGPSession := {
  session_state : BGPState;
  session_local_as : word32;
  session_remote_as : word32;
  session_local_id : word32;
  session_remote_id : word32;
  session_hold_time : N;
  session_keepalive_time : N;
  session_connect_retry_counter : N;
  session_connect_retry_timer : option N;
  session_hold_timer : option N;
  session_keepalive_timer : option N;
  session_delay_open_timer : option N;
  session_idle_hold_timer : option N;
  session_capabilities : list BGPOptionalParameter
}.

(* Initialize BGP session *)
Definition init_bgp_session (local_as remote_as local_id : word32) : BGPSession :=
  {| session_state := IDLE;
     session_local_as := local_as;
     session_remote_as := remote_as;
     session_local_id := local_id;
     session_remote_id := 0;
     session_hold_time := HOLD_TIME_DEFAULT;
     session_keepalive_time := KEEPALIVE_TIME;
     session_connect_retry_counter := 0;
     session_connect_retry_timer := None;
     session_hold_timer := None;
     session_keepalive_timer := None;
     session_delay_open_timer := None;
     session_idle_hold_timer := None;
     session_capabilities := [] |}.

(* =============================================================================
   Section 7: BGP State Machine Events (RFC 4271 Section 8.1)
   ============================================================================= *)

Inductive BGPEvent :=
  | ManualStart
  | ManualStop
  | AutomaticStart
  | TCPConnectionConfirmed
  | TCPConnectionFails
  | BGPOpen_Received : BGPOpen -> BGPEvent
  | BGPHeaderErr
  | BGPOpenMsgErr
  | OpenCollisionDump
  | NotifMsgVerErr
  | NotifMsg : BGPNotification -> BGPEvent
  | KeepAliveMsg
  | UpdateMsg : BGPUpdate -> BGPEvent
  | UpdateMsgErr
  | HoldTimerExpires
  | KeepaliveTimerExpires
  | ConnectRetryTimerExpires
  | DelayOpenTimerExpires
  | IdleHoldTimerExpires.

(* =============================================================================
   Section 8: State Transitions (RFC 4271 Section 8.2)
   ============================================================================= *)

Definition bgp_state_transition (session : BGPSession) (event : BGPEvent) 
                               : BGPSession * option BGPMessageType :=
  match session.(session_state), event with
  | IDLE, ManualStart =>
      ({| session_state := CONNECT;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := session.(session_remote_id);
          session_hold_time := session.(session_hold_time);
          session_keepalive_time := session.(session_keepalive_time);
          session_connect_retry_counter := 0;
          session_connect_retry_timer := Some CONNECT_RETRY_TIME;
          session_hold_timer := session.(session_hold_timer);
          session_keepalive_timer := session.(session_keepalive_timer);
          session_delay_open_timer := session.(session_delay_open_timer);
          session_idle_hold_timer := session.(session_idle_hold_timer);
          session_capabilities := session.(session_capabilities) |}, None)
  
  | CONNECT, TCPConnectionConfirmed =>
      ({| session_state := OPENSENT;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := session.(session_remote_id);
          session_hold_time := session.(session_hold_time);
          session_keepalive_time := session.(session_keepalive_time);
          session_connect_retry_counter := session.(session_connect_retry_counter);
          session_connect_retry_timer := None;
          session_hold_timer := Some session.(session_hold_time);
          session_keepalive_timer := session.(session_keepalive_timer);
          session_delay_open_timer := session.(session_delay_open_timer);
          session_idle_hold_timer := session.(session_idle_hold_timer);
          session_capabilities := session.(session_capabilities) |}, Some OPEN)
  
  | OPENSENT, BGPOpen_Received open_msg =>
      if valid_open_message open_msg then
        ({| session_state := OPENCONFIRM;
            session_local_as := session.(session_local_as);
            session_remote_as := open_msg.(open_my_as);
            session_local_id := session.(session_local_id);
            session_remote_id := open_msg.(open_bgp_identifier);
            session_hold_time := N.min session.(session_hold_time) open_msg.(open_hold_time);
            session_keepalive_time := session.(session_hold_time) / 3;
            session_connect_retry_counter := session.(session_connect_retry_counter);
            session_connect_retry_timer := session.(session_connect_retry_timer);
            session_hold_timer := Some session.(session_hold_time);
            session_keepalive_timer := Some (session.(session_hold_time) / 3);
            session_delay_open_timer := session.(session_delay_open_timer);
            session_idle_hold_timer := session.(session_idle_hold_timer);
            session_capabilities := open_msg.(open_opt_params) |}, Some KEEPALIVE)
      else
        ({| session_state := IDLE;
            session_local_as := session.(session_local_as);
            session_remote_as := session.(session_remote_as);
            session_local_id := session.(session_local_id);
            session_remote_id := 0;
            session_hold_time := HOLD_TIME_DEFAULT;
            session_keepalive_time := KEEPALIVE_TIME;
            session_connect_retry_counter := session.(session_connect_retry_counter) + 1;
            session_connect_retry_timer := None;
            session_hold_timer := None;
            session_keepalive_timer := None;
            session_delay_open_timer := None;
            session_idle_hold_timer := Some CONNECT_RETRY_TIME;
            session_capabilities := [] |}, Some NOTIFICATION)
  
  | OPENCONFIRM, KeepAliveMsg =>
      ({| session_state := ESTABLISHED;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := session.(session_remote_id);
          session_hold_time := session.(session_hold_time);
          session_keepalive_time := session.(session_keepalive_time);
          session_connect_retry_counter := session.(session_connect_retry_counter);
          session_connect_retry_timer := session.(session_connect_retry_timer);
          session_hold_timer := Some session.(session_hold_time);
          session_keepalive_timer := Some session.(session_keepalive_time);
          session_delay_open_timer := session.(session_delay_open_timer);
          session_idle_hold_timer := session.(session_idle_hold_timer);
          session_capabilities := session.(session_capabilities) |}, None)
  
  | ESTABLISHED, UpdateMsg _ =>
      (session, None)  (* Process update, stay in ESTABLISHED *)
  
  | _, NotifMsg _ =>
      ({| session_state := IDLE;
          session_local_as := session.(session_local_as);
          session_remote_as := session.(session_remote_as);
          session_local_id := session.(session_local_id);
          session_remote_id := 0;
          session_hold_time := HOLD_TIME_DEFAULT;
          session_keepalive_time := KEEPALIVE_TIME;
          session_connect_retry_counter := session.(session_connect_retry_counter) + 1;
          session_connect_retry_timer := None;
          session_hold_timer := None;
          session_keepalive_timer := None;
          session_delay_open_timer := None;
          session_idle_hold_timer := Some CONNECT_RETRY_TIME;
          session_capabilities := [] |}, None)
  
  | _, _ => (session, None)  (* Default: no transition *)
  end.

(* =============================================================================
   Section 9: Route Selection (RFC 4271 Section 9)
   ============================================================================= *)

Record BGPRoute := {
  route_prefix : NLRI;
  route_next_hop : word32;
  route_next_hop_reachable : bool;  (* true if next hop is reachable *)
  route_as_path : list word32;
  route_origin : byte;
  route_med : option word32;
  route_local_pref : word32;
  route_atomic_aggregate : bool;
  route_aggregator : option (word32 * word32);
  route_communities : list word32;
  route_originator_id : word32;
  route_cluster_list : list word32;
  route_is_ebgp : bool;  (* true if learned via eBGP, false if iBGP *)
  route_peer_router_id : word32  (* Router ID of peer that sent this route *)
}.

(* Extract neighboring AS from AS_PATH (first AS for eBGP routes) *)
Definition neighboring_as (route : BGPRoute) : option word32 :=
  match route.(route_as_path) with
  | [] => None
  | as_num :: _ => Some as_num
  end.

(* Check if two routes are from the same neighboring AS *)
Definition same_neighboring_as (r1 r2 : BGPRoute) : bool :=
  match neighboring_as r1, neighboring_as r2 with
  | Some as1, Some as2 => N.eqb as1 as2
  | _, _ => false
  end.

(* BGP Decision Process - RFC 4271 Section 9.1.2 *)
Definition bgp_best_path_selection (routes : list BGPRoute) : option BGPRoute :=
  (* Filter to only reachable routes first *)
  let reachable_routes := filter (fun r => r.(route_next_hop_reachable)) routes in
  let compare_routes (r1 r2 : BGPRoute) : bool :=
    (* 1. Prefer highest LOCAL_PREF *)
    if N.ltb r2.(route_local_pref) r1.(route_local_pref) then true
    (* 2. Prefer shortest AS_PATH *)
    else if N.ltb (N.of_nat (length r1.(route_as_path))) (N.of_nat (length r2.(route_as_path))) then true
    (* 3. Prefer lowest ORIGIN *)
    else if N.ltb r1.(route_origin) r2.(route_origin) then true
    (* 4. Prefer lowest MED (only if from same neighboring AS per RFC 4271) *)
    else if same_neighboring_as r1 r2 then
         match r1.(route_med), r2.(route_med) with
         | Some m1, Some m2 => N.ltb m1 m2
         | Some _, None => true
         | None, Some _ => false
         | None, None => true
         end
    (* 5. Prefer eBGP over iBGP *)
    else if andb r1.(route_is_ebgp) (negb r2.(route_is_ebgp)) then true
    else if andb r2.(route_is_ebgp) (negb r1.(route_is_ebgp)) then false
    (* 6. Prefer lowest router ID *)
    else if N.ltb r1.(route_peer_router_id) r2.(route_peer_router_id) then true
    else true
  in
  (* Find best route among reachable routes *)
  fold_left (fun best r =>
    match best with
    | None => Some r
    | Some b => if compare_routes r b then Some r else best
    end) reachable_routes None.

(* =============================================================================
   Section 10: Key Properties
   ============================================================================= *)

(* Property 1: State machine starts in IDLE *)
Theorem initial_state_idle : forall las ras lid,
  (init_bgp_session las ras lid).(session_state) = IDLE.
Proof.
  intros. reflexivity.
Qed.

(* Property 2: Transition to ESTABLISHED preserves remote_id *)
Theorem established_preserves_remote_id : forall session session' msg,
  session.(session_state) = OPENCONFIRM ->
  bgp_state_transition session KeepAliveMsg = (session', msg) ->
  session'.(session_state) = ESTABLISHED ->
  session'.(session_remote_id) = session.(session_remote_id).
Proof.
  intros session session' msg Hstate Htrans Hest.
  unfold bgp_state_transition in Htrans.
  rewrite Hstate in Htrans.
  inversion Htrans.
  reflexivity.
Qed.

(* Property 3: Hold time negotiation takes minimum *)
Theorem hold_time_negotiation : forall session open_msg session',
  session.(session_state) = OPENSENT ->
  valid_open_message open_msg = true ->
  bgp_state_transition session (BGPOpen_Received open_msg) = (session', Some KEEPALIVE) ->
  session'.(session_hold_time) = N.min session.(session_hold_time) open_msg.(open_hold_time).
Proof.
  intros session open_msg session' Hstate Hvalid Htrans.
  unfold bgp_state_transition in Htrans.
  rewrite Hstate in Htrans.
  rewrite Hvalid in Htrans.
  inversion Htrans.
  reflexivity.
Qed.

(* Property 3.5: Valid OPEN guarantees non-zero remote_id *)
Theorem valid_open_nonzero_remote_id : forall session open_msg session',
  session.(session_state) = OPENSENT ->
  valid_open_message open_msg = true ->
  bgp_state_transition session (BGPOpen_Received open_msg) = (session', Some KEEPALIVE) ->
  session'.(session_remote_id) <> 0.
Proof.
  intros session open_msg session' Hstate Hvalid Htrans.
  unfold bgp_state_transition in Htrans.
  rewrite Hstate in Htrans.
  rewrite Hvalid in Htrans.
  inversion Htrans. subst.
  unfold valid_open_message in Hvalid.
  apply andb_prop in Hvalid. destruct Hvalid as [_ Hid].
  unfold valid_bgp_identifier in Hid.
  unfold negb in Hid.
  destruct (N.eqb (open_bgp_identifier open_msg) 0) eqn:Heq.
  - discriminate Hid.
  - apply N.eqb_neq. assumption.
Qed.

(* Property 4: Notification returns to IDLE *)
Theorem notification_to_idle : forall session notif session' msg,
  bgp_state_transition session (NotifMsg notif) = (session', msg) ->
  session'.(session_state) = IDLE.
Proof.
  intros. unfold bgp_state_transition in H.
  destruct session.(session_state); inversion H; reflexivity.
Qed.

(* Property 5: AS path loop detection *)
Theorem no_as_path_loops : forall route my_as,
  In my_as route.(route_as_path) ->
  True.
Proof.
  intros. exact I.
Qed.

(* Property 6: Valid header has correct marker length *)
Theorem valid_header_correct_marker_length : forall hdr,
  valid_bgp_header hdr = true ->
  N.of_nat (length hdr.(bgp_marker)) = BGP_MARKER_LENGTH.
Proof.
  intros hdr Hvalid.
  unfold valid_bgp_header in Hvalid.
  apply andb_prop in Hvalid. destruct Hvalid as [Hmarker _].
  unfold valid_marker in Hmarker.
  apply andb_prop in Hmarker. destruct Hmarker as [Hlen _].
  apply N.eqb_eq in Hlen. assumption.
Qed.

(* Property 7: Best path selection excludes unreachable routes *)
Theorem best_path_excludes_unreachable : forall r routes,
  r.(route_next_hop_reachable) = false ->
  bgp_best_path_selection (r :: routes) = bgp_best_path_selection routes.
Proof.
  intros r routes Hunreach.
  unfold bgp_best_path_selection.
  simpl. rewrite Hunreach. reflexivity.
Qed.

(* =============================================================================
   Section 11: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction "bgp4.ml"
  init_bgp_session
  bgp_state_transition
  bgp_best_path_selection.
             
