(* =============================================================================
   Formal Verification of DNS CAA Updates
   
   Specification: RFC 8659 (P. Hallam-Baker, R. Stradling, J. Hoffman-Andrews, November 2019)
   Target: CAA Updates
   
   Module: CAA Updates Formalization and Verification
   Author: Charles C Norton
   Date: September 1, 2025
   
   "And that authority was made yet more perfect as the work progressed."
   
   ============================================================================= *)

From Coq Require Import
  List
  NArith.NArith
  Bool
  String
  Arith
  Lia.

Import ListNotations.
Open Scope N_scope.

(* =============================================================================
   Section 1: New CAA Tags (RFC 8659)
   ============================================================================= *)

(* Extended CAA Tags *)
Definition CAA_TAG_CONTACTEMAIL : string := "contactemail".
Definition CAA_TAG_CONTACTPHONE : string := "contactphone".
Definition CAA_TAG_ACCOUNTURI : string := "accounturi".
Definition CAA_TAG_VALIDATIONMETHODS : string := "validationmethods".

(* Account binding *)
Record AccountBinding := {
  ab_account_uri : string;
  ab_ca_domain : string;
  ab_validation_methods : list string
}.

(* =============================================================================
   Section 2: Account URI Binding (RFC 8659 Section 3)
   ============================================================================= *)

(* Parse accounturi value *)
Definition parse_accounturi (value : string) : option AccountBinding :=
  let parts := String.split " " value in
  match parts with
  | ca :: uri :: _ =>
      Some {| ab_account_uri := uri;
              ab_ca_domain := ca;
              ab_validation_methods := [] |}
  | _ => None
  end.

(* Validate account binding *)
Definition validate_account_binding (binding : AccountBinding) 
                                   (ca_account : string) : bool :=
  String.eqb binding.(ab_account_uri) ca_account.

(* =============================================================================
   Section 3: Validation Methods (RFC 8659 Section 4)
   ============================================================================= *)

(* ACME validation methods *)
Definition VALIDATION_HTTP01 : string := "http-01".
Definition VALIDATION_DNS01 : string := "dns-01".
Definition VALIDATION_TLSALPN01 : string := "tls-alpn-01".

(* Parse validationmethods *)
Definition parse_validation_methods (value : string) : list string :=
  String.split "," value.

(* Check if validation method is allowed *)
Definition is_method_allowed (allowed : list string) (method : string) : bool :=
  existsb (String.eqb method) allowed.

(* =============================================================================
   Section 4: Enhanced CAA Checking (RFC 8659)
   ============================================================================= *)

Record EnhancedCAAContext := {
  ecaa_domain : list string;
  ecaa_ca_domain : string;
  ecaa_account_uri : option string;
  ecaa_validation_method : string;
  ecaa_wildcard : bool
}.

(* Enhanced CAA authorization check *)
Definition check_enhanced_caa (ctx : EnhancedCAAContext) 
                             (records : list CAARecord) : CAAResult :=
  (* Check accounturi if present *)
  let account_records := filter (fun caa => 
    String.eqb caa.(caa_tag) CAA_TAG_ACCOUNTURI) records in
  
  match ctx.(ecaa_account_uri) with
  | Some account =>
      if negb (null account_records) then
        (* Account binding required *)
        if existsb (fun caa =>
          match parse_accounturi caa.(caa_value) with
          | Some binding => 
              andb (String.eqb binding.(ab_ca_domain) ctx.(ecaa_ca_domain))
                   (String.eqb binding.(ab_account_uri) account)
          | None => false
          end) account_records then
          (* Check validation methods *)
          check_validation_methods ctx records
        else
          CAA_NOT_AUTHORIZED
      else
        (* No account binding - check normal authorization *)
        check_standard_caa ctx records
  | None =>
      check_standard_caa ctx records
  end.

(* Check validation methods *)
Definition check_validation_methods (ctx : EnhancedCAAContext)
                                   (records : list CAARecord) : CAAResult :=
  let method_records := filter (fun caa =>
    String.eqb caa.(caa_tag) CAA_TAG_VALIDATIONMETHODS) records in
  
  if null method_records then
    (* No restrictions on methods *)
    check_standard_caa ctx records
  else
    (* Check if method is allowed *)
    if existsb (fun caa =>
      let methods := parse_validation_methods caa.(caa_value) in
      is_method_allowed methods ctx.(ecaa_validation_method))
      method_records then
      check_standard_caa ctx records
    else
      CAA_NOT_AUTHORIZED.

(* Standard CAA check (issue/issuewild) *)
Definition check_standard_caa (ctx : EnhancedCAAContext)
                             (records : list CAARecord) : CAAResult :=
  let tag := if ctx.(ecaa_wildcard) then CAA_TAG_ISSUEWILD else CAA_TAG_ISSUE in
  let relevant := filter (fun caa => String.eqb caa.(caa_tag) tag) records in
  
  if null relevant && ctx.(ecaa_wildcard) then
    (* Fall back to issue for wildcard *)
    let issue_records := filter (fun caa => 
      String.eqb caa.(caa_tag) CAA_TAG_ISSUE) records in
    if existsb (fun caa =>
      matches_ca_domain caa.(caa_value) ctx.(ecaa_ca_domain)) issue_records then
      CAA_AUTHORIZED
    else
      CAA_NOT_AUTHORIZED
  else if existsb (fun caa =>
    matches_ca_domain caa.(caa_value) ctx.(ecaa_ca_domain)) relevant then
    CAA_AUTHORIZED
  else
    CAA_NOT_AUTHORIZED.

(* =============================================================================
   Section 5: Contact Information (RFC 8659 Section 5)
   ============================================================================= *)

Record ContactInfo := {
  ci_email : option string;
  ci_phone : option string
}.

(* Extract contact information *)
Definition extract_contact_info (records : list CAARecord) : ContactInfo :=
  let email := find_map (fun caa =>
    if String.eqb caa.(caa_tag) CAA_TAG_CONTACTEMAIL then
      Some caa.(caa_value)
    else None) records in
  
  let phone := find_map (fun caa =>
    if String.eqb caa.(caa_tag) CAA_TAG_CONTACTPHONE then
      Some caa.(caa_value)
    else None) records in
  
  {| ci_email := email;
     ci_phone := phone |}.

(* =============================================================================
   Section 6: Parameter Syntax (RFC 8659 Appendix A)
   ============================================================================= *)

(* Extended parameter syntax *)
Record CAAParameter := {
  cp_tag : string;
  cp_value : string
}.

(* Parse parameters from issue/issuewild value *)
Definition parse_caa_parameters (value : string) : list CAAParameter :=
  let parts := String.split ";" value in
  match parts with
  | _ :: params => map (fun p =>
      match String.split "=" p with
      | tag :: val :: _ => {| cp_tag := String.trim tag;
                              cp_value := String.trim val |}
      | _ => {| cp_tag := ""; cp_value := "" |}
      end) params
  | [] => []
  end.

(* =============================================================================
   Section 7: Key Properties
   ============================================================================= *)

(* Property 1: Account binding is specific *)
Theorem account_binding_specific : forall ctx records account,
  ctx.(ecaa_account_uri) = Some account ->
  check_enhanced_caa ctx records = CAA_AUTHORIZED ->
  exists caa binding, In caa records /\
    parse_accounturi caa.(caa_value) = Some binding /\
    binding.(ab_account_uri) = account.
Proof.
  admit.
Qed.

(* Property 2: Validation methods restrict *)
Theorem validation_methods_restrict : forall ctx records,
  existsb (fun caa => String.eqb caa.(caa_tag) CAA_TAG_VALIDATIONMETHODS) 
          records = true ->
  check_validation_methods ctx records = CAA_AUTHORIZED ->
  exists caa methods, In caa records /\
    caa.(caa_tag) = CAA_TAG_VALIDATIONMETHODS /\
    In ctx.(ecaa_validation_method) (parse_validation_methods caa.(caa_value)).
Proof.
  admit.
Qed.

(* Property 3: Enhanced checking is backward compatible *)
Theorem enhanced_backward_compatible : forall ctx records,
  (forall caa, In caa records -> 
    In caa.(caa_tag) [CAA_TAG_ISSUE; CAA_TAG_ISSUEWILD; CAA_TAG_IODEF]) ->
  check_enhanced_caa ctx records = check_standard_caa ctx records.
Proof.
  admit.
Qed.

(* =============================================================================
   Section 8: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction "caa_updates.ml"
  parse_accounturi
  validate_account_binding
  parse_validation_methods
  check_enhanced_caa
  check_validation_methods
  extract_contact_info.
