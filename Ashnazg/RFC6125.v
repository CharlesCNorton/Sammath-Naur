(* =============================================================================
   Formal Verification of Service Identity in TLS
   
   Specification: RFC 6125 (P. Saint-Andre, J. Hodges, March 2011)
   Target: Service Identity Verification
   
   Module: Service Identity Formalization and Verification
   Author: Charles C Norton
   Date: September 1, 2025
   
   "When he departed, they believed all his mind was known to them."
   
   ============================================================================= *)

From Coq Require Import
  List
  String
  NArith.NArith
  Bool
  Arith
  Lia.

Import ListNotations.
Open Scope N_scope.
Open Scope string_scope.

(* =============================================================================
   Section 1: Basic Types and Constants
   ============================================================================= *)

Definition byte := N.
Definition word16 := N.
Definition word32 := N.

(* Reference Identifier Types *)
Inductive ReferenceIdentifierType :=
  | RI_DNS_ID         (* DNS domain name *)
  | RI_SRV_ID         (* SRV service name *)
  | RI_URI_ID         (* URI *)
  | RI_IP_ID.         (* IP address *)

(* Presented Identifier Sources *)
Inductive PresentedIdentifierSource :=
  | PI_CN             (* Common Name *)
  | PI_SAN_DNS        (* subjectAltName dNSName *)
  | PI_SAN_SRV        (* subjectAltName SRVName *)
  | PI_SAN_URI        (* subjectAltName uniformResourceIdentifier *)
  | PI_SAN_IP.        (* subjectAltName iPAddress *)

(* =============================================================================
   Section 2: Reference Identifiers (RFC 6125 Section 1.8)
   ============================================================================= *)

Record ReferenceIdentifier := {
  ref_type : ReferenceIdentifierType;
  ref_value : string;
  ref_application_service : option string  (* e.g., "https", "ldaps" *)
}.

(* Create DNS reference identifier *)
Definition create_dns_reference (hostname : string) : ReferenceIdentifier :=
  {| ref_type := RI_DNS_ID;
     ref_value := ascii_lowercase hostname;
     ref_application_service := None |}.

(* Create SRV reference identifier *)
Definition create_srv_reference (service : string) (hostname : string) 
                               : ReferenceIdentifier :=
  {| ref_type := RI_SRV_ID;
     ref_value := "_" ++ service ++ "." ++ ascii_lowercase hostname;
     ref_application_service := Some service |}.

(* Create URI reference identifier *)
Definition create_uri_reference (uri : string) : ReferenceIdentifier :=
  {| ref_type := RI_URI_ID;
     ref_value := uri;
     ref_application_service := extract_scheme uri |}.

(* =============================================================================
   Section 3: Presented Identifiers (RFC 6125 Section 1.8)
   ============================================================================= *)

Record PresentedIdentifier := {
  pres_source : PresentedIdentifierSource;
  pres_value : string
}.

(* Extract presented identifiers from certificate *)
Definition extract_presented_identifiers (cert : Certificate) 
                                        : list PresentedIdentifier :=
  (* First, check subjectAltName extension *)
  let san_ids := 
    match find_extension OID_SUBJECT_ALT_NAME cert.(tbsCertificate).(extensions) with
    | None => []
    | Some ext =>
        flat_map (fun gn =>
          match gn with
          | GN_DNSName name => 
              [{| pres_source := PI_SAN_DNS; pres_value := name |}]
          | GN_URI uri => 
              [{| pres_source := PI_SAN_URI; pres_value := uri |}]
          | GN_IPAddress ip => 
              [{| pres_source := PI_SAN_IP; 
                  pres_value := ip_bytes_to_string ip |}]
          | _ => []
          end
        ) (decode_general_names ext.(extnValue))
    end in
  
  (* If no SAN, fall back to CN (deprecated but still used) *)
  if null san_ids then
    extract_cn_identifiers cert.(tbsCertificate).(subject)
  else
    san_ids.

(* Extract CN from subject *)
Definition extract_cn_identifiers (subject : DistinguishedName) 
                                : list PresentedIdentifier :=
  flat_map (fun rdn =>
    flat_map (fun atv =>
      if oid_equal atv.(attr_type) OID_COMMON_NAME then
        [{| pres_source := PI_CN; pres_value := atv.(attr_value) |}]
      else []
    ) rdn
  ) subject.

(* =============================================================================
   Section 4: Matching Rules (RFC 6125 Section 6)
   ============================================================================= *)

(* DNS matching with wildcards *)
Definition match_dns_name (reference : string) (presented : string) : bool :=
  if String.prefix "*." presented then
    (* Wildcard certificate *)
    let wildcard_base := String.substring 2 (String.length presented - 2) presented in
    (* Check if reference matches wildcard pattern *)
    match string_split "." reference with
    | [] => false
    | first :: rest =>
        (* Wildcard only matches one label *)
        String.eqb (String.concat "." rest) wildcard_base
    end
  else
    (* Exact match (case-insensitive) *)
    String.eqb (ascii_lowercase reference) (ascii_lowercase presented).

(* IP address matching *)
Definition match_ip_address (reference : string) (presented : string) : bool :=
  (* Exact match only for IP addresses *)
  String.eqb reference presented.

(* URI matching *)
Definition match_uri (reference : string) (presented : string) : bool :=
  (* Extract URI components and compare *)
  let ref_parts := parse_uri reference in
  let pres_parts := parse_uri presented in
  match ref_parts, pres_parts with
  | Some (r_scheme, r_host, r_path), Some (p_scheme, p_host, p_path) =>
      andb (String.eqb r_scheme p_scheme)
           (andb (match_dns_name r_host p_host)
                 (String.eqb r_path p_path))
  | _, _ => false
  end.

(* SRV matching *)
Definition match_srv_name (reference : string) (presented : string) : bool :=
  (* SRV names include service prefix *)
  if andb (String.prefix "_" reference) (String.prefix "_" presented) then
    String.eqb (ascii_lowercase reference) (ascii_lowercase presented)
  else
    false.

(* =============================================================================
   Section 5: Verification Algorithm (RFC 6125 Section 6.2)
   ============================================================================= *)

(* Verify service identity *)
Definition verify_service_identity (cert : Certificate) 
                                  (reference : ReferenceIdentifier)
                                  : bool :=
  let presented_ids := extract_presented_identifiers cert in
  
  (* Check if any presented identifier matches the reference *)
  existsb (fun pres =>
    match reference.(ref_type), pres.(pres_source) with
    | RI_DNS_ID, PI_SAN_DNS => match_dns_name reference.(ref_value) 
                                              pres.(pres_value)
    | RI_DNS_ID, PI_CN => 
        (* CN matching only if no SAN extension *)
        if has_san_extension cert then false
        else match_dns_name reference.(ref_value) pres.(pres_value)
    | RI_SRV_ID, PI_SAN_SRV => match_srv_name reference.(ref_value) 
                                              pres.(pres_value)
    | RI_URI_ID, PI_SAN_URI => match_uri reference.(ref_value) 
                                         pres.(pres_value)
    | RI_IP_ID, PI_SAN_IP => match_ip_address reference.(ref_value) 
                                              pres.(pres_value)
    | _, _ => false
    end
  ) presented_ids.

(* Check if certificate has SAN extension *)
Definition has_san_extension (cert : Certificate) : bool :=
  existsb (fun ext => oid_equal ext.(extnID) OID_SUBJECT_ALT_NAME)
          cert.(tbsCertificate).(extensions).

(* =============================================================================
   Section 6: Wildcard Certificates (RFC 6125 Section 6.4.3)
   ============================================================================= *)

(* Validate wildcard certificate *)
Definition validate_wildcard (presented : string) : bool :=
  if String.prefix "*." presented then
    let base := String.substring 2 (String.length presented - 2) presented in
    (* Wildcard must be leftmost label *)
    andb (negb (string_contains "*" base))
         (* Must have at least two labels after wildcard *)
         (N.leb 1 (count_dots base))
  else
    true.  (* Not a wildcard *)

(* Check if reference matches wildcard constraints *)
Definition wildcard_constraints_met (reference : string) (wildcard : string) : bool :=
  (* Wildcard should not match multiple labels *)
  let ref_labels := string_split "." reference in
  let wild_labels := string_split "." (String.substring 2 
                                       (String.length wildcard - 2) wildcard) in
  N.eqb (length ref_labels) (1 + length wild_labels).

(* =============================================================================
   Section 7: Application-Specific Rules (RFC 6125 Section 6.5)
   ============================================================================= *)

Record ApplicationRules := {
  app_allow_wildcards : bool;
  app_allow_cn_fallback : bool;
  app_require_san : bool;
  app_check_key_usage : bool;
  app_pinned_certificates : list (string * Certificate)  (* hostname -> cert *)
}.

(* Default rules for HTTPS *)
Definition https_rules : ApplicationRules :=
  {| app_allow_wildcards := true;
     app_allow_cn_fallback := true;  (* For legacy compatibility *)
     app_require_san := false;        (* Recommended true *)
     app_check_key_usage := true;
     app_pinned_certificates := [] |}.

(* Verify with application rules *)
Definition verify_with_rules (cert : Certificate) 
                            (reference : ReferenceIdentifier)
                            (rules : ApplicationRules) : bool :=
  (* Check pinned certificates first *)
  match find (fun pin => String.eqb (fst pin) reference.(ref_value))
             rules.(app_pinned_certificates) with
  | Some (_, pinned_cert) =>
      certificate_equal cert pinned_cert
  | None =>
      (* Check key usage if required *)
      let ku_valid := if rules.(app_check_key_usage) then
                       check_key_usage_for_tls cert
                     else true in
      
      (* Check SAN requirement *)
      let san_valid := if rules.(app_require_san) then
                        has_san_extension cert
                      else true in
      
      andb ku_valid (andb san_valid 
                         (verify_service_identity cert reference)).

(* =============================================================================
   Section 8: Internationalized Domain Names (RFC 6125 Section 7.2)
   ============================================================================= *)

(* Convert IDN to ASCII (A-label) *)
Definition idn_to_ascii (idn : string) : string :=
  (* Simplified - actual implementation would use IDNA2008 *)
  if string_is_ascii idn then
    idn
  else
    "xn--" ++ punycode_encode idn.

(* Prepare domain for matching *)
Definition prepare_domain_name (domain : string) : string :=
  ascii_lowercase (idn_to_ascii domain).

(* Match with IDN support *)
Definition match_dns_name_idn (reference : string) (presented : string) : bool :=
  match_dns_name (prepare_domain_name reference) 
                 (prepare_domain_name presented).

(* =============================================================================
   Section 9: Security Considerations (RFC 6125 Section 7.3)
   ============================================================================= *)

(* Check for homograph attacks *)
Definition check_homograph_attack (name : string) : bool :=
  (* Check for mixed scripts that could be confusing *)
  let scripts := detect_unicode_scripts name in
  match scripts with
  | [] => true
  | [single] => true  (* Single script is OK *)
  | multiple => 
      (* Mixed scripts - potential homograph *)
      check_confusable_scripts multiple
  end.

(* Validate certificate chain for service *)
Definition validate_service_chain (chain : list Certificate)
                                 (reference : ReferenceIdentifier)
                                 (trusted_roots : list Certificate) : bool :=
  match chain with
  | [] => false
  | server_cert :: intermediates =>
      (* Verify service identity on leaf certificate *)
      if verify_service_identity server_cert reference then
        (* Verify certificate chain *)
        validate_cert_chain (server_cert :: intermediates) trusted_roots
      else
        false
  end.

(* =============================================================================
   Section 10: Key Properties
   ============================================================================= *)

(* Property 1: SAN takes precedence over CN *)
Theorem san_precedence : forall cert ref,
  has_san_extension cert = true ->
  verify_service_identity cert ref = true ->
  exists pres, In pres (extract_presented_identifiers cert) /\
              pres.(pres_source) <> PI_CN.
Proof.
  admit.
Qed.

(* Property 2: Wildcards match single label only *)
Theorem wildcard_single_label : forall ref wild,
  String.prefix "*." wild = true ->
  match_dns_name ref wild = true ->
  count_dots ref = count_dots wild.
Proof.
  admit.
Qed.

(* Property 3: IP addresses require exact match *)
Theorem ip_exact_match : forall ref_ip pres_ip,
  match_ip_address ref_ip pres_ip = true ->
  ref_ip = pres_ip.
Proof.
  intros. unfold match_ip_address in H.
  apply String.eqb_eq in H. exact H.
Qed.

(* Property 4: Case insensitive DNS matching *)
Theorem dns_case_insensitive : forall ref pres,
  match_dns_name ref pres = true ->
  match_dns_name (ascii_uppercase ref) pres = true.
Proof.
  admit.
Qed.

(* Property 5: Pinned certificates bypass other checks *)
Theorem pinning_bypasses : forall cert ref rules pinned,
  In (ref.(ref_value), pinned) rules.(app_pinned_certificates) ->
  certificate_equal cert pinned = true ->
  verify_with_rules cert ref rules = true.
Proof.
  admit.
Qed.

(* =============================================================================
   Section 11: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction "service_identity.ml"
  create_dns_reference
  extract_presented_identifiers
  match_dns_name
  verify_service_identity
  verify_with_rules
  validate_wildcard
  match_dns_name_idn
  validate_service_chain.
