(******************************************************************************)
(*                                                                            *)
(*             SAML: Security Assertion Markup Language 2.0                   *)
(*                                                                            *)
(*     Formal verification of SAML 2.0 assertions per OASIS standard.         *)
(*     Encodes assertion structure, conditions, subject confirmation,         *)
(*     and signature validation for federated identity.                       *)
(*                                                                            *)
(*     "They became Ringwraiths, shadows under his great Shadow,              *)
(*      his most terrible servants."                                          *)
(*     - J.R.R. Tolkien, The Silmarillion                                     *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 5, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Coq Require Import
  List
  String
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
Definition word32 := N.
Definition word64 := N.

(* SAML Version *)
Definition SAML_VERSION_20 : string := "2.0".

(* Name Identifier Formats *)
Inductive NameIDFormat :=
  | UNSPECIFIED
  | EMAIL_ADDRESS
  | X509_SUBJECT_NAME
  | WINDOWS_DOMAIN_QUALIFIED
  | KERBEROS
  | ENTITY
  | PERSISTENT
  | TRANSIENT.

(* Subject Confirmation Methods *)
Inductive ConfirmationMethod :=
  | HOLDER_OF_KEY
  | SENDER_VOUCHES
  | BEARER.

(* Status Codes *)
Inductive StatusCode :=
  | SUCCESS
  | REQUESTER
  | RESPONDER
  | VERSION_MISMATCH
  | AUTHN_FAILED
  | NO_AUTHN_CONTEXT.

