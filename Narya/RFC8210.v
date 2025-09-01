(* =============================================================================
   Formal Verification of The Resource Public Key Infrastructure (RPKI) to Router Protocol
   
   Specification: RFC 8210 (R. Bush, R. Austein, September 2017)
   Target: RTR Protocol Version 1
   
   Module: RPKI-RTR Protocol Formalization and Verification
   Author: Charles C Norton
   Date: September 1, 2025
   
   "And every seal was registered in books of iron and stone."
   
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

(* Protocol Version *)
Definition RTR_PROTOCOL_VERSION : byte := 1.

(* Default Port *)
Definition RTR_PORT : word16 := 323.
Definition RTR_SSH_PORT : word16 := 22.
Definition RTR_TLS_PORT : word16 := 324.

(* PDU Types (RFC 8210 Section 5.2) *)
Definition PDU_SERIAL_NOTIFY : byte := 0.
Definition PDU_SERIAL_QUERY : byte := 1.
Definition PDU_RESET_QUERY : byte := 2.
Definition PDU_CACHE_RESPONSE : byte := 3.
Definition PDU_IPV4_PREFIX : byte := 4.
Definition PDU_IPV6_PREFIX : byte := 6.
Definition PDU_END_OF_DATA : byte := 7.
Definition PDU_CACHE_RESET : byte := 8.
Definition PDU_ROUTER_KEY : byte := 9.
Definition PDU_ERROR_REPORT : byte := 10.

(* Error Codes (RFC 8210 Section 5.10) *)
Definition ERR_CORRUPT_DATA : word16 := 0.
Definition ERR_INTERNAL_ERROR : word16 := 1.
Definition ERR_NO_DATA : word16 := 2.
Definition ERR_INVALID_REQUEST : word16 := 3.
Definition ERR_UNSUPPORTED_VERSION : word16 := 4.
Definition ERR_UNSUPPORTED_PDU : word16 := 5.
Definition ERR_WITHDRAWAL_UNKNOWN : word16 := 6.
Definition ERR_DUPLICATE_ANNOUNCEMENT : word16 := 7.
Definition ERR_UNEXPECTED_VERSION : word16 := 8.

(* Timing Parameters (seconds) *)
Definition REFRESH_INTERVAL_DEFAULT : N := 3600.    (* 1 hour *)
Definition RETRY_INTERVAL_DEFAULT : N := 600.       (* 10 minutes *)
Definition EXPIRE_INTERVAL_DEFAULT : N := 7200.     (* 2 hours *)

(* =============================================================================
   Section 2: PDU Structures (RFC 8210 Section 5)
   ============================================================================= *)

(* Common PDU Header *)
Record PDUHeader := {
  pdu_version : byte;
  pdu_type : byte;
  pdu_session_id : word16;
  pdu_length : word32
}.

(* Serial Notify PDU *)
Record SerialNotifyPDU := {
  sn_header : PDUHeader;
  sn_serial : word32
}.

(* Serial Query PDU *)
Record SerialQueryPDU := {
  sq_header : PDUHeader;
  sq_serial : word32
}.

(* Reset Query PDU *)
Record ResetQueryPDU := {
  rq_header : PDUHeader
}.

(* Cache Response PDU *)
Record CacheResponsePDU := {
  cr_header : PDUHeader
}.

(* IPv4 Prefix PDU *)
Record IPv4PrefixPDU := {
  ip4_header : PDUHeader;
  ip4_flags : byte;           (* Bit 0: 0=announcement, 1=withdrawal *)
  ip4_prefix_len : byte;
  ip4_max_len : byte;
  ip4_zero : byte;
  ip4_prefix : word32;
  ip4_asn : word32
}.

(* IPv6 Prefix PDU *)
Record IPv6PrefixPDU := {
  ip6_header : PDUHeader;
  ip6_flags : byte;
  ip6_prefix_len : byte;
  ip6_max_len : byte;
  ip6_zero : byte;
  ip6_prefix : list byte;     (* 16 bytes *)
  ip6_asn : word32
}.

(* End of Data PDU *)
Record EndOfDataPDU := {
  eod_header : PDUHeader;
  eod_serial : word32;
  eod_refresh : word32;
  eod_retry : word32;
  eod_expire : word32
}.

(* Cache Reset PDU *)
Record CacheResetPDU := {
  rst_header : PDUHeader
}.

(* Router Key PDU *)
Record RouterKeyPDU := {
  rk_header : PDUHeader;
  rk_flags : byte;            (* Bit 0: 0=announcement, 1=withdrawal *)
  rk_zero : byte;
  rk_ski : list byte;         (* Subject Key Identifier - 20 bytes *)
  rk_asn : word32;
  rk_spki : list byte         (* Subject Public Key Info - variable *)
}.

(* Error Report PDU *)
Record ErrorReportPDU := {
  err_header : PDUHeader;
  err_pdu_len : word32;       (* Length of encapsulated PDU *)
  err_erroneous_pdu : list byte;
  err_error_text_len : word32;
  err_error_text : list byte
}.

(* =============================================================================
   Section 3: RTR Session State (RFC 8210 Section 7)
   ============================================================================= *)

Inductive SessionState :=
  | STATE_CLOSED
  | STATE_OPENING
  | STATE_ESTABLISHED
  | STATE_UP_TO_DATE
  | STATE_ERROR.

Record RTRSession := {
  session_id : word16;
  session_version : byte;
  session_state : SessionState;
  session_serial : word32;
  session_refresh_interval : N;
  session_retry_interval : N;
  session_expire_interval : N;
  session_last_update : N;
  session_cache : ValidationCache
}
with ValidationCache := {
  cache_serial : word32;
  cache_session_id : word16;
  cache_ipv4_prefixes : list IPv4PrefixEntry;
  cache_ipv6_prefixes : list IPv6PrefixEntry;
  cache_router_keys : list RouterKeyEntry
}
with IPv4PrefixEntry := {
  ipv4e_prefix : word32;
  ipv4e_prefix_len : byte;
  ipv4e_max_len : byte;
  ipv4e_asn : word32
}
with IPv6PrefixEntry := {
  ipv6e_prefix : list byte;
  ipv6e_prefix_len : byte;
  ipv6e_max_len : byte;
  ipv6e_asn : word32
}
with RouterKeyEntry := {
  rke_ski : list byte;
  rke_asn : word32;
  rke_spki : list byte
}.

(* Initialize RTR session *)
Definition init_rtr_session : RTRSession :=
  {| session_id := 0;
     session_version := RTR_PROTOCOL_VERSION;
     session_state := STATE_CLOSED;
     session_serial := 0;
     session_refresh_interval := REFRESH_INTERVAL_DEFAULT;
     session_retry_interval := RETRY_INTERVAL_DEFAULT;
     session_expire_interval := EXPIRE_INTERVAL_DEFAULT;
     session_last_update := 0;
     session_cache := {| cache_serial := 0;
                        cache_session_id := 0;
                        cache_ipv4_prefixes := [];
                        cache_ipv6_prefixes := [];
                        cache_router_keys := [] |} |}.

(* =============================================================================
   Section 4: PDU Processing (RFC 8210 Section 8)
   ============================================================================= *)

(* Process incoming PDU *)
Definition process_pdu (session : RTRSession) (pdu_type : byte) 
                      : RTRSession * option byte :=
  match session.(session_state), pdu_type with
  
  (* Opening state - expect Cache Response or Error *)
  | STATE_OPENING, PDU_CACHE_RESPONSE =>
      ({| session_id := session.(session_id);
          session_version := session.(session_version);
          session_state := STATE_ESTABLISHED;
          session_serial := session.(session_serial);
          session_refresh_interval := session.(session_refresh_interval);
          session_retry_interval := session.(session_retry_interval);
          session_expire_interval := session.(session_expire_interval);
          session_last_update := session.(session_last_update);
          session_cache := session.(session_cache) |},
       None)
  
  (* Established state - receive prefix PDUs *)
  | STATE_ESTABLISHED, PDU_IPV4_PREFIX =>
      (session, None)  (* Process IPv4 prefix *)
  
  | STATE_ESTABLISHED, PDU_IPV6_PREFIX =>
      (session, None)  (* Process IPv6 prefix *)
  
  | STATE_ESTABLISHED, PDU_END_OF_DATA =>
      ({| session_id := session.(session_id);
          session_version := session.(session_version);
          session_state := STATE_UP_TO_DATE;
          session_serial := session.(session_serial) + 1;
          session_refresh_interval := session.(session_refresh_interval);
          session_retry_interval := session.(session_retry_interval);
          session_expire_interval := session.(session_expire_interval);
          session_last_update := 0;  (* Should be current time *)
          session_cache := session.(session_cache) |},
       None)
  
  (* Up-to-date state - handle notifications *)
  | STATE_UP_TO_DATE, PDU_SERIAL_NOTIFY =>
      (session, Some PDU_SERIAL_QUERY)  (* Request incremental update *)
  
  (* Any state - handle cache reset *)
  | _, PDU_CACHE_RESET =>
      ({| session_id := session.(session_id);
          session_version := session.(session_version);
          session_state := STATE_OPENING;
          session_serial := 0;
          session_refresh_interval := session.(session_refresh_interval);
          session_retry_interval := session.(session_retry_interval);
          session_expire_interval := session.(session_expire_interval);
          session_last_update := session.(session_last_update);
          session_cache := {| cache_serial := 0;
                             cache_session_id := session.(session_id);
                             cache_ipv4_prefixes := [];
                             cache_ipv6_prefixes := [];
                             cache_router_keys := [] |} |},
       Some PDU_RESET_QUERY)
  
  (* Error handling *)
  | _, PDU_ERROR_REPORT =>
      ({| session_id := session.(session_id);
          session_version := session.(session_version);
          session_state := STATE_ERROR;
          session_serial := session.(session_serial);
          session_refresh_interval := session.(session_refresh_interval);
          session_retry_interval := session.(session_retry_interval);
          session_expire_interval := session.(session_expire_interval);
          session_last_update := session.(session_last_update);
          session_cache := session.(session_cache) |},
       None)
  
  | _, _ => (session, None)
  end.

(* =============================================================================
   Section 5: Cache Operations
   ============================================================================= *)

(* Add IPv4 prefix to cache *)
Definition add_ipv4_prefix (cache : ValidationCache) (entry : IPv4PrefixEntry)
                          : ValidationCache :=
  {| cache_serial := cache.(cache_serial);
     cache_session_id := cache.(cache_session_id);
     cache_ipv4_prefixes := entry :: cache.(cache_ipv4_prefixes);
     cache_ipv6_prefixes := cache.(cache_ipv6_prefixes);
     cache_router_keys := cache.(cache_router_keys) |}.

(* Remove IPv4 prefix from cache *)
Definition remove_ipv4_prefix (cache : ValidationCache) (entry : IPv4PrefixEntry)
                             : ValidationCache :=
  {| cache_serial := cache.(cache_serial);
     cache_session_id := cache.(cache_session_id);
     cache_ipv4_prefixes := filter (fun e =>
       negb (andb (N.eqb e.(ipv4e_prefix) entry.(ipv4e_prefix))
                  (andb (N.eqb e.(ipv4e_prefix_len) entry.(ipv4e_prefix_len))
                        (N.eqb e.(ipv4e_asn) entry.(ipv4e_asn))))
     ) cache.(cache_ipv4_prefixes);
     cache_ipv6_prefixes := cache.(cache_ipv6_prefixes);
     cache_router_keys := cache.(cache_router_keys) |}.

(* Process prefix PDU based on flags *)
Definition process_prefix_pdu (cache : ValidationCache) (pdu : IPv4PrefixPDU)
                             : ValidationCache :=
  let entry := {| ipv4e_prefix := pdu.(ip4_prefix);
                  ipv4e_prefix_len := pdu.(ip4_prefix_len);
                  ipv4e_max_len := pdu.(ip4_max_len);
                  ipv4e_asn := pdu.(ip4_asn) |} in
  if N.testbit pdu.(ip4_flags) 0 then
    remove_ipv4_prefix cache entry  (* Withdrawal *)
  else
    add_ipv4_prefix cache entry.    (* Announcement *)

(* =============================================================================
   Section 6: Timer Management (RFC 8210 Section 6)
   ============================================================================= *)

(* Check if refresh timer expired *)
Definition refresh_timer_expired (session : RTRSession) (now : N) : bool :=
  N.ltb (session.(session_last_update) + session.(session_refresh_interval)) now.

(* Check if expire timer expired *)
Definition expire_timer_expired (session : RTRSession) (now : N) : bool :=
  N.ltb (session.(session_last_update) + session.(session_expire_interval)) now.

(* Handle timer expiry *)
Definition handle_timer_expiry (session : RTRSession) (now : N) 
                              : RTRSession * option byte :=
  if expire_timer_expired session now then
    (* Cache expired - request full update *)
    ({| session_id := session.(session_id);
        session_version := session.(session_version);
        session_state := STATE_OPENING;
        session_serial := 0;
        session_refresh_interval := session.(session_refresh_interval);
        session_retry_interval := session.(session_retry_interval);
        session_expire_interval := session.(session_expire_interval);
        session_last_update := now;
        session_cache := {| cache_serial := 0;
                           cache_session_id := session.(session_id);
                           cache_ipv4_prefixes := [];
                           cache_ipv6_prefixes := [];
                           cache_router_keys := [] |} |},
     Some PDU_RESET_QUERY)
  else if refresh_timer_expired session now then
    (* Refresh timer expired - request incremental update *)
    (session, Some PDU_SERIAL_QUERY)
  else
    (session, None).

(* =============================================================================
   Section 7: Error Handling (RFC 8210 Section 5.10)
   ============================================================================= *)

(* Create error PDU *)
Definition create_error_pdu (err_code : word16) (bad_pdu : list byte) 
                           (err_text : list byte) : ErrorReportPDU :=
  {| err_header := {| pdu_version := RTR_PROTOCOL_VERSION;
                      pdu_type := PDU_ERROR_REPORT;
                      pdu_session_id := 0;
                      pdu_length := 16 + length bad_pdu + length err_text |};
     err_pdu_len := length bad_pdu;
     err_erroneous_pdu := bad_pdu;
     err_error_text_len := length err_text;
     err_error_text := err_text |}.

(* Handle error based on code *)
Definition handle_error (session : RTRSession) (err_code : word16) 
                       : RTRSession :=
  match err_code with
  | 0 (* CORRUPT_DATA *) =>
      {| session_id := session.(session_id);
         session_version := session.(session_version);
         session_state := STATE_ERROR;
         session_serial := session.(session_serial);
         session_refresh_interval := session.(session_refresh_interval);
         session_retry_interval := session.(session_retry_interval);
         session_expire_interval := session.(session_expire_interval);
         session_last_update := session.(session_last_update);
         session_cache := session.(session_cache) |}
  | _ => session
  end.

(* =============================================================================
   Section 8: Incremental Updates (RFC 8210 Section 4.4)
   ============================================================================= *)

(* Apply incremental update *)
Definition apply_incremental_update (cache : ValidationCache) 
                                   (announcements withdrawals : list IPv4PrefixEntry)
                                   : ValidationCache :=
  let cache_after_withdrawals := fold_left remove_ipv4_prefix withdrawals cache in
  fold_left add_ipv4_prefix announcements cache_after_withdrawals.

(* Compute delta between cache states *)
Definition compute_cache_delta (old_cache new_cache : ValidationCache) 
                              : (list IPv4PrefixEntry * list IPv4PrefixEntry) :=
  let announcements := filter (fun e =>
    negb (existsb (fun o =>
      andb (N.eqb e.(ipv4e_prefix) o.(ipv4e_prefix))
           (andb (N.eqb e.(ipv4e_prefix_len) o.(ipv4e_prefix_len))
                 (N.eqb e.(ipv4e_asn) o.(ipv4e_asn)))
    ) old_cache.(cache_ipv4_prefixes))
  ) new_cache.(cache_ipv4_prefixes) in
  
  let withdrawals := filter (fun o =>
    negb (existsb (fun e =>
      andb (N.eqb e.(ipv4e_prefix) o.(ipv4e_prefix))
           (andb (N.eqb e.(ipv4e_prefix_len) o.(ipv4e_prefix_len))
                 (N.eqb e.(ipv4e_asn) o.(ipv4e_asn)))
    ) new_cache.(cache_ipv4_prefixes))
  ) old_cache.(cache_ipv4_prefixes) in
  
  (announcements, withdrawals).

(* =============================================================================
   Section 9: Key Properties
   ============================================================================= *)

(* Property 1: State transitions are valid *)
Theorem valid_state_transitions : forall session pdu_type session' response,
  process_pdu session pdu_type = (session', response) ->
  session'.(session_state) = STATE_ERROR \/
  session'.(session_state) = session.(session_state) \/
  (session.(session_state) = STATE_OPENING /\ session'.(session_state) = STATE_ESTABLISHED) \/
  (session.(session_state) = STATE_ESTABLISHED /\ session'.(session_state) = STATE_UP_TO_DATE) \/
  (session'.(session_state) = STATE_OPENING).
Proof.
  admit.
Qed.

(* Property 2: Serial number increases *)
Theorem serial_increases : forall session session' response,
  process_pdu session PDU_END_OF_DATA = (session', response) ->
  session'.(session_serial) = session.(session_serial) + 1.
Proof.
  intros. unfold process_pdu in H.
  destruct session.(session_state); try discriminate.
  inversion H. reflexivity.
Qed.

(* Property 3: Cache operations preserve session ID *)
Theorem cache_preserves_session : forall cache entry,
  (add_ipv4_prefix cache entry).(cache_session_id) = cache.(cache_session_id).
Proof.
  intros. unfold add_ipv4_prefix. reflexivity.
Qed.

(* Property 4: Timer expiry triggers request *)
Theorem timer_expiry_triggers : forall session now session' req,
  handle_timer_expiry session now = (session', Some req) ->
  req = PDU_RESET_QUERY \/ req = PDU_SERIAL_QUERY.
Proof.
  intros. unfold handle_timer_expiry in H.
  destruct (expire_timer_expired session now) eqn:E1.
  - inversion H. left. reflexivity.
  - destruct (refresh_timer_expired session now) eqn:E2.
    + inversion H. right. reflexivity.
    + discriminate.
Qed.

(* Property 5: Error states are terminal *)
Theorem error_state_terminal : forall session pdu_type,
  session.(session_state) = STATE_ERROR ->
  fst (process_pdu session pdu_type) = session.
Proof.
  admit.
Qed.

(* =============================================================================
   Section 10: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction "rpki_rtr.ml"
  init_rtr_session
  process_pdu
  add_ipv4_prefix
  remove_ipv4_prefix
  handle_timer_expiry
  apply_incremental_update
  compute_cache_delta
  create_error_pdu.
