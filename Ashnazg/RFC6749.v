(******************************************************************************)
(*                                                                            *)
(*                  OAuth: Authorization Framework (RFC 6749)                 *)
(*                                                                            *)
(*     Formal verification of OAuth 2.0 authorization flows. Encodes grant    *)
(*     types, token lifecycle, scope validation, and redirect URI matching.   *)
(*                                                                            *)
(*     "Nine he gave to Mortal Men, proud and great, and so ensnared them."   *)
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
Definition word16 := N.
Definition word32 := N.

(* Grant Types (RFC 6749 Section 1.3) *)
Inductive GrantType :=
  | AUTHORIZATION_CODE
  | IMPLICIT
  | RESOURCE_OWNER_PASSWORD
  | CLIENT_CREDENTIALS
  | REFRESH_TOKEN
  | EXTENSION_GRANT.

(* Token Types (RFC 6749 Section 7.1) *)
Inductive TokenType :=
  | BEARER
  | MAC.

(* Error Codes (RFC 6749 Section 4.1.2.1) *)
Inductive AuthErrorCode :=
  | INVALID_REQUEST
  | UNAUTHORIZED_CLIENT
  | ACCESS_DENIED
  | UNSUPPORTED_RESPONSE_TYPE
  | INVALID_SCOPE
  | SERVER_ERROR
  | TEMPORARILY_UNAVAILABLE.

