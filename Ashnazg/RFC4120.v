(******************************************************************************)
(*                                                                            *)
(*         Kerberos: The Network Authentication Service (Version 5)           *)
(*                                                                            *)
(*     Formal verification of RFC 4120. Encodes AS/TGS exchanges, ticket      *)
(*     structure, authenticator validation, and cross-realm referral.         *)
(*                                                                            *)
(*     "As soon as Sauron set the One Ring upon his finger they were aware    *)
(*      of him; and they knew him."                                           *)
(*     - J.R.R. Tolkien, The Silmarillion                                     *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 5, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

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

Definition KRB5_PORT : word16 := 88.
Definition PVNO : byte := 5.

Definition KRB_AS_REQ : byte := 10.
Definition KRB_AS_REP : byte := 11.
Definition KRB_TGS_REQ : byte := 12.
Definition KRB_TGS_REP : byte := 13.
Definition KRB_AP_REQ : byte := 14.
Definition KRB_AP_REP : byte := 15.
Definition KRB_ERROR : byte := 30.

