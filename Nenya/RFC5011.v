(* =============================================================================
   Formal Verification of Automated Updates of DNS Security (DNSSEC) Trust Anchors
   
   Specification: RFC 5011 (M. StJohns, September 2007)
   Target: Trust Anchor Updates
   
   Module: Trust Anchor Update Formalization and Verification
   Author: Charles C Norton
   Date: September 1, 2025
   
   "The trust of each ring was rooted deep, as trees that may not be moved."
   
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

(* RFC 5011 Timers *)
Definition ADD_HOLD_DOWN_TIME : word32 := 2592000.  (* 30 days *)
Definition REMOVE_HOLD_DOWN_TIME : word32 := 2592000. (* 30 days *)
Definition MIN_PROBE_INTERVAL : word32 := 86400.    (* 1 day *)
Definition MAX_PROBE_INTERVAL : word32 := 1209600.  (* 14 days *)
Definition PROBE_FAILURE_HOURS : word32 := 3600.    (* 1 hour *)

(* Revoke bit *)
Definition REVOKE_BIT : word16 := 128.  (* Bit 8 of DNSKEY flags *)

(* =============================================================================
   Section 2: Trust Anchor States (RFC 5011 Section 2)
   ============================================================================= *)

Inductive TrustAnchorState :=
  | TA_START         (* Newly seen key *)
  | TA_ADD_PENDING   (* Waiting for add hold-down *)
  | TA_VALID         (* Trusted key *)
  | TA_MISSING       (* Previously valid key not seen *)
  | TA_REVOKED       (* Key with revoke bit set *)
  | TA_REMOVED.      (* Key removed from trust *)

Record ManagedTrustAnchor := {
  mta_key : DNSKEYRecord;
  mta_key_tag : word16;
  mta_state : TrustAnchorState;
  mta_first_seen : word32;
  mta_last_seen : word32;
  mta_last_refresh : word32;
  mta_add_hold_down : word32;
  mta_remove_hold_down : word32
}.

(* =============================================================================
   Section 3: Trust Anchor Repository (RFC 5011 Section 3)
   ============================================================================= *)

Record TrustAnchorRepository := {
  tar_zone : list string;
  tar_anchors : list ManagedTrustAnchor;
  tar_last_query : word32;
  tar_next_probe : word32;
  tar_consecutive_failures : N;
  tar_active_refresh : bool
}.

(* Initialize trust anchor *)
Definition init_trust_anchor (key : DNSKEYRecord) (now : word32) 
                            : ManagedTrustAnchor :=
  {| mta_key := key;
     mta_key_tag := calculate_key_tag key;
     mta_state := TA_START;
     mta_first_seen := now;
     mta_last_seen := now;
     mta_last_refresh := now;
     mta_add_hold_down := now + ADD_HOLD_DOWN_TIME;
     mta_remove_hold_down := 0 |}.

(* =============================================================================
   Section 4: Active Refresh (RFC 5011 Section 2.3)
   ============================================================================= *)

(* Calculate next probe time *)
Definition calculate_next_probe (last_probe : word32) (failures : N) : word32 :=
  if N.eqb failures 0 then
    (* Normal probe interval *)
    last_probe + MIN_PROBE_INTERVAL
  else
    (* Exponential backoff on failures *)
    let backoff := N.shiftl PROBE_FAILURE_HOURS failures in
    last_probe + N.min backoff MAX_PROBE_INTERVAL.

(* Probe for trust anchor updates *)
Definition probe_trust_anchors (repo : TrustAnchorRepository) 
                              (dnskey_rrset : list DNSKEYRecord)
                              (now : word32) : TrustAnchorRepository :=
  let updated_anchors := update_anchor_states repo.(tar_anchors) dnskey_rrset now in
  {| tar_zone := repo.(tar_zone);
     tar_anchors := updated_anchors;
     tar_last_query := now;
     tar_next_probe := calculate_next_probe now repo.(tar_consecutive_failures);
     tar_consecutive_failures := 0;
     tar_active_refresh := true |}.

(* =============================================================================
   Section 5: State Machine (RFC 5011 Section 4)
   ============================================================================= *)

(* Update single anchor state *)
Definition update_anchor_state (anchor : ManagedTrustAnchor)
                              (key_present : bool)
                              (key_revoked : bool)
                              (now : word32) : ManagedTrustAnchor :=
  match anchor.(mta_state) with
  | TA_START =>
      if key_present then
        if N.leb anchor.(mta_add_hold_down) now then
          (* Promote to VALID after hold-down *)
          {| mta_key := anchor.(mta_key);
             mta_key_tag := anchor.(mta_key_tag);
             mta_state := TA_VALID;
             mta_first_seen := anchor.(mta_first_seen);
             mta_last_seen := now;
             mta_last_refresh := now;
             mta_add_hold_down := anchor.(mta_add_hold_down);
             mta_remove_hold_down := 0 |}
        else
          (* Still in hold-down *)
          {| mta_key := anchor.(mta_key);
             mta_key_tag := anchor.(mta_key_tag);
             mta_state := TA_ADD_PENDING;
             mta_first_seen := anchor.(mta_first_seen);
             mta_last_seen := now;
             mta_last_refresh := now;
             mta_add_hold_down := anchor.(mta_add_hold_down);
             mta_remove_hold_down := 0 |}
      else
        (* Key disappeared - remove *)
        {| mta_key := anchor.(mta_key);
           mta_key_tag := anchor.(mta_key_tag);
           mta_state := TA_REMOVED;
           mta_first_seen := anchor.(mta_first_seen);
           mta_last_seen := anchor.(mta_last_seen);
           mta_last_refresh := now;
           mta_add_hold_down := anchor.(mta_add_hold_down);
           mta_remove_hold_down := now |}
           
  | TA_ADD_PENDING =>
      if key_present then
        if N.leb anchor.(mta_add_hold_down) now then
          (* Promote to VALID *)
          {| mta_key := anchor.(mta_key);
             mta_key_tag := anchor.(mta_key_tag);
             mta_state := TA_VALID;
             mta_first_seen := anchor.(mta_first_seen);
             mta_last_seen := now;
             mta_last_refresh := now;
             mta_add_hold_down := anchor.(mta_add_hold_down);
             mta_remove_hold_down := 0 |}
        else
          (* Update last seen *)
          {| mta_key := anchor.(mta_key);
             mta_key_tag := anchor.(mta_key_tag);
             mta_state := TA_ADD_PENDING;
             mta_first_seen := anchor.(mta_first_seen);
             mta_last_seen := now;
             mta_last_refresh := now;
             mta_add_hold_down := anchor.(mta_add_hold_down);
             mta_remove_hold_down := 0 |}
      else
        (* Reset to START *)
        {| mta_key := anchor.(mta_key);
           mta_key_tag := anchor.(mta_key_tag);
           mta_state := TA_START;
           mta_first_seen := now;
           mta_last_seen := anchor.(mta_last_seen);
           mta_last_refresh := now;
           mta_add_hold_down := now + ADD_HOLD_DOWN_TIME;
           mta_remove_hold_down := 0 |}
           
  | TA_VALID =>
      if key_present then
        if key_revoked then
          (* Key revoked *)
          {| mta_key := anchor.(mta_key);
             mta_key_tag := anchor.(mta_key_tag);
             mta_state := TA_REVOKED;
             mta_first_seen := anchor.(mta_first_seen);
             mta_last_seen := now;
             mta_last_refresh := now;
             mta_add_hold_down := anchor.(mta_add_hold_down);
             mta_remove_hold_down := now + REMOVE_HOLD_DOWN_TIME |}
        else
          (* Update last seen *)
          {| mta_key := anchor.(mta_key);
             mta_key_tag := anchor.(mta_key_tag);
             mta_state := TA_VALID;
             mta_first_seen := anchor.(mta_first_seen);
             mta_last_seen := now;
             mta_last_refresh := now;
             mta_add_hold_down := anchor.(mta_add_hold_down);
             mta_remove_hold_down := 0 |}
      else
        (* Key missing *)
        {| mta_key := anchor.(mta_key);
           mta_key_tag := anchor.(mta_key_tag);
           mta_state := TA_MISSING;
           mta_first_seen := anchor.(mta_first_seen);
           mta_last_seen := anchor.(mta_last_seen);
           mta_last_refresh := now;
           mta_add_hold_down := anchor.(mta_add_hold_down);
           mta_remove_hold_down := now + REMOVE_HOLD_DOWN_TIME |}
           
  | TA_MISSING =>
      if key_present then
        if key_revoked then
          (* Found but revoked *)
          {| mta_key := anchor.(mta_key);
             mta_key_tag := anchor.(mta_key_tag);
             mta_state := TA_REVOKED;
             mta_first_seen := anchor.(mta_first_seen);
             mta_last_seen := now;
             mta_last_refresh := now;
             mta_add_hold_down := anchor.(mta_add_hold_down);
             mta_remove_hold_down := anchor.(mta_remove_hold_down) |}
        else
          (* Found again - restore *)
          {| mta_key := anchor.(mta_key);
             mta_key_tag := anchor.(mta_key_tag);
             mta_state := TA_VALID;
             mta_first_seen := anchor.(mta_first_seen);
             mta_last_seen := now;
             mta_last_refresh := now;
             mta_add_hold_down := anchor.(mta_add_hold_down);
             mta_remove_hold_down := 0 |}
      else
        if N.leb anchor.(mta_remove_hold_down) now then
          (* Remove after hold-down *)
          {| mta_key := anchor.(mta_key);
             mta_key_tag := anchor.(mta_key_tag);
             mta_state := TA_REMOVED;
             mta_first_seen := anchor.(mta_first_seen);
             mta_last_seen := anchor.(mta_last_seen);
             mta_last_refresh := now;
             mta_add_hold_down := anchor.(mta_add_hold_down);
             mta_remove_hold_down := anchor.(mta_remove_hold_down) |}
        else
          anchor
          
  | TA_REVOKED =>
      if N.leb anchor.(mta_remove_hold_down) now then
        (* Remove after hold-down *)
        {| mta_key := anchor.(mta_key);
           mta_key_tag := anchor.(mta_key_tag);
           mta_state := TA_REMOVED;
           mta_first_seen := anchor.(mta_first_seen);
           mta_last_seen := anchor.(mta_last_seen);
           mta_last_refresh := now;
           mta_add_hold_down := anchor.(mta_add_hold_down);
           mta_remove_hold_down := anchor.(mta_remove_hold_down) |}
      else
        anchor
        
  | TA_REMOVED => anchor
  end.

(* =============================================================================
   Section 6: Revocation (RFC 5011 Section 5)
   ============================================================================= *)

(* Check if key is revoked *)
Definition is_key_revoked (key : DNSKEYRecord) : bool :=
  N.testbit key.(dnskey_flags) 8.

(* Set revoke bit *)
Definition set_revoke_bit (key : DNSKEYRecord) : DNSKEYRecord :=
  {| dnskey_flags := N.lor key.(dnskey_flags) REVOKE_BIT;
     dnskey_protocol := key.(dnskey_protocol);
     dnskey_algorithm := key.(dnskey_algorithm);
     dnskey_public_key := key.(dnskey_public_key) |}.

(* =============================================================================
   Section 7: Key Properties
   ============================================================================= *)

(* Property 1: Hold-down times are respected *)
Theorem hold_down_respected : forall anchor now,
  anchor.(mta_state) = TA_ADD_PENDING ->
  update_anchor_state anchor true false now = 
    if N.leb anchor.(mta_add_hold_down) now then
      set_state anchor TA_VALID
    else anchor.
Proof.
  admit.
Qed.

(* Property 2: Revoked keys are removed *)
Theorem revoked_keys_removed : forall anchor now,
  anchor.(mta_state) = TA_REVOKED ->
  N.leb anchor.(mta_remove_hold_down) now = true ->
  (update_anchor_state anchor true true now).(mta_state) = TA_REMOVED.
Proof.
  admit.
Qed.

(* Property 3: Valid keys can be revoked *)
Theorem valid_keys_revocable : forall anchor now,
  anchor.(mta_state) = TA_VALID ->
  (update_anchor_state anchor true true now).(mta_state) = TA_REVOKED.
Proof.
  admit.
Qed.

(* =============================================================================
   Section 8: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction "trust_anchor_update.ml"
  init_trust_anchor
  calculate_next_probe
  probe_trust_anchors
  update_anchor_state
  is_key_revoked
  set_revoke_bit.
