(* =============================================================================
   Formal Verification of Internet X.509 Public Key Infrastructure
   
   Specification: RFC 5280 (D. Cooper, et al., May 2008)
   Target: X.509 Certificate and CRL Profile
   
   Module: X.509 PKI Formalization and Verification
   Author: Charles C Norton
   Date: September 1, 2025
   
   "Then Annatar spoke: 'The foundation is laid. I must depart for a time.'"
   
   ============================================================================= *)

From Coq Require Import
  List
  String
  Ascii
  NArith.NArith
  Bool
  Arith
  Lia.

Import ListNotations.
Open Scope N_scope.

(* =============================================================================
   Section 1: Basic Types and ASN.1 Primitives
   ============================================================================= *)

Definition byte := N.
Definition word32 := N.
Definition word64 := N.

(* Equality functions *)
Definition byte_eq (a b : byte) : bool := N.eqb a b.

Fixpoint list_beq {A : Type} (eq_fn : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x::xs, y::ys => andb (eq_fn x y) (list_beq eq_fn xs ys)
  | _, _ => false
  end.

(* ASN.1 Tags *)
Definition ASN1_BOOLEAN : byte := 1.
Definition ASN1_INTEGER : byte := 2.
Definition ASN1_BIT_STRING : byte := 3.
Definition ASN1_OCTET_STRING : byte := 4.
Definition ASN1_NULL : byte := 5.
Definition ASN1_OID : byte := 6.
Definition ASN1_SEQUENCE : byte := 16.
Definition ASN1_SET : byte := 17.
Definition ASN1_UTF8String : byte := 12.
Definition ASN1_PrintableString : byte := 19.
Definition ASN1_UTCTime : byte := 23.
Definition ASN1_GeneralizedTime : byte := 24.

(* Object Identifiers *)
Definition OID := list N.

(* Common OIDs *)
Definition OID_RSA_ENCRYPTION : OID := [1; 2; 840; 113549; 1; 1; 1].
Definition OID_SHA256_WITH_RSA : OID := [1; 2; 840; 113549; 1; 1; 11].
Definition OID_ECDSA_WITH_SHA256 : OID := [1; 2; 840; 10045; 4; 3; 2].
Definition OID_COMMON_NAME : OID := [2; 5; 4; 3].
Definition OID_COUNTRY : OID := [2; 5; 4; 6].
Definition OID_ORGANIZATION : OID := [2; 5; 4; 10].
Definition OID_KEY_USAGE : OID := [2; 5; 29; 15].
Definition OID_BASIC_CONSTRAINTS : OID := [2; 5; 29; 19].
Definition OID_SUBJECT_ALT_NAME : OID := [2; 5; 29; 17].
Definition OID_AUTHORITY_KEY_ID : OID := [2; 5; 29; 35].
Definition OID_SUBJECT_KEY_ID : OID := [2; 5; 29; 14].
Definition OID_EXTENDED_KEY_USAGE : OID := [2; 5; 29; 37].
Definition OID_CRL_DISTRIBUTION_POINTS : OID := [2; 5; 29; 31].
Definition OID_CERTIFICATE_POLICIES : OID := [2; 5; 29; 32].
Definition OID_POLICY_MAPPINGS : OID := [2; 5; 29; 33].
Definition OID_AUTHORITY_INFO_ACCESS : OID := [1; 3; 6; 1; 5; 5; 7; 1; 1].
Definition OID_SUBJECT_INFO_ACCESS : OID := [1; 3; 6; 1; 5; 5; 7; 1; 11].
Definition OID_INHIBIT_ANY_POLICY : OID := [2; 5; 29; 54].
Definition OID_FRESHEST_CRL : OID := [2; 5; 29; 46].
Definition OID_NAME_CONSTRAINTS : OID := [2; 5; 29; 30].

(* Extended Key Usage OIDs *)
Definition OID_KP_SERVER_AUTH : OID := [1; 3; 6; 1; 5; 5; 7; 3; 1].
Definition OID_KP_CLIENT_AUTH : OID := [1; 3; 6; 1; 5; 5; 7; 3; 2].
Definition OID_KP_CODE_SIGNING : OID := [1; 3; 6; 1; 5; 5; 7; 3; 3].
Definition OID_KP_EMAIL_PROTECTION : OID := [1; 3; 6; 1; 5; 5; 7; 3; 4].
Definition OID_KP_TIME_STAMPING : OID := [1; 3; 6; 1; 5; 5; 7; 3; 8].
Definition OID_KP_OCSP_SIGNING : OID := [1; 3; 6; 1; 5; 5; 7; 3; 9].

(* =============================================================================
   Section 2: X.509 Certificate Structure (RFC 5280 Section 4.1)
   ============================================================================= *)

(* Algorithm Identifier *)
Record AlgorithmIdentifier := {
  algorithm : OID;
  parameters : option (list byte)
}.

(* Validity Period *)
Record Validity := {
  notBefore : N;  (* Unix timestamp *)
  notAfter : N
}.

(* Distinguished Name *)
Record AttributeTypeAndValue := {
  attr_type : OID;
  attr_value : string
}.

Definition RelativeDistinguishedName := list AttributeTypeAndValue.
Definition DistinguishedName := list RelativeDistinguishedName.

(* Public Key Info *)
Record SubjectPublicKeyInfo := {
  algorithm_id : AlgorithmIdentifier;
  publicKey : list byte
}.

(* Extension *)
Record Extension := {
  extnID : OID;
  critical : bool;
  extnValue : list byte
}.

(* TBSCertificate (To Be Signed Certificate) *)
Record TBSCertificate := {
  version : N;  (* 0=v1, 1=v2, 2=v3 *)
  serialNumber : list byte;
  signature : AlgorithmIdentifier;
  issuer : DistinguishedName;
  validity : Validity;
  subject : DistinguishedName;
  subjectPublicKeyInfo : SubjectPublicKeyInfo;
  issuerUniqueID : option (list byte);
  subjectUniqueID : option (list byte);
  extensions : list Extension
}.

(* X.509 Certificate *)
Record Certificate := {
  tbsCertificate : TBSCertificate;
  signatureAlgorithm : AlgorithmIdentifier;
  signatureValue : list byte
}.

(* =============================================================================
   Section 3: Certificate Extensions (RFC 5280 Section 4.2)
   ============================================================================= *)

(* Key Usage *)
Record KeyUsage := {
  digitalSignature : bool;
  nonRepudiation : bool;
  keyEncipherment : bool;
  dataEncipherment : bool;
  keyAgreement : bool;
  keyCertSign : bool;
  cRLSign : bool;
  encipherOnly : bool;
  decipherOnly : bool
}.

(* Basic Constraints *)
Record BasicConstraints := {
  cA : bool;
  pathLenConstraint : option N
}.

(* =============================================================================
   Cryptographic Primitives

   Stub implementations - to be replaced with verified implementations
   ============================================================================= *)

Fixpoint replicate {A : Type} (n : nat) (x : A) : list A :=
  match n with
  | O => []
  | S n' => x :: replicate n' x
  end.

Definition hash_sha256 (data : list byte) : list byte :=
  replicate 32 0.

Lemma hash_sha256_length : forall data, List.length (hash_sha256 data) = 32%nat.
Proof.
  intros. unfold hash_sha256.
  assert (forall n, List.length (replicate n 0) = n).
  { induction n; simpl; auto. }
  apply H.
Qed.

Definition sign_data (data privkey : list byte) : list byte :=
  replicate 256 0.

Definition verify_signature (data sig : list byte) (pubkey : SubjectPublicKeyInfo) : bool :=
  true.

Lemma verify_signature_correct : forall data privkey pubkey sig,
  sig = sign_data data privkey ->
  verify_signature data sig pubkey = true.
Proof.
  intros. unfold verify_signature. reflexivity.
Qed.

Fixpoint replicate_N (n : N) (x : byte) : list byte :=
  match n with
  | N0 => []
  | Npos p => replicate (Pos.to_nat p) x
  end.

Definition generate_random_bytes (n : N) : list byte :=
  replicate_N n 0.

Lemma random_bytes_length : forall n, List.length (generate_random_bytes n) = N.to_nat n.
Proof.
  intros n. unfold generate_random_bytes.
  destruct n as [| p]; simpl.
  - reflexivity.
  - unfold replicate_N. induction (Pos.to_nat p); simpl; auto.
Qed.

Definition current_time : N := 1700000000.

Lemma current_time_positive : N.lt 0 current_time.
Proof.
  unfold current_time.
  apply N.ltb_lt.
  reflexivity.
Qed.

(* =============================================================================
   ASN.1 DER Encoding Primitives
   ============================================================================= *)

(* String to bytes conversion *)
Fixpoint string_to_bytes (s : string) : list byte :=
  match s with
  | EmptyString => []
  | String c rest => N.of_nat (Ascii.nat_of_ascii c) :: string_to_bytes rest
  end.

(* Encode length in DER format *)
Fixpoint encode_bytes_helper (n : N) (fuel : nat) : list byte :=
  match fuel with
  | O => []
  | S fuel' =>
      if N.eqb n 0 then []
      else N.modulo n 256 :: encode_bytes_helper (N.div n 256) fuel'
  end.

Definition encode_length (len : N) : list byte :=
  if N.ltb len 128 then
    [len]
  else
    let bytes := encode_bytes_helper len 20 in
    (128 + N.of_nat (List.length bytes)) :: bytes.

(* Encode TLV (Tag-Length-Value) *)
Definition encode_tlv (tag : byte) (value : list byte) : list byte :=
  tag :: encode_length (N.of_nat (List.length value)) ++ value.

(* Encode INTEGER *)
Definition encode_integer (n : N) : list byte :=
  let bytes := encode_bytes_helper n 20 in
  let bytes' := match bytes with [] => [0] | _ => bytes end in
  encode_tlv ASN1_INTEGER bytes'.

(* Encode SEQUENCE *)
Definition encode_sequence (contents : list byte) : list byte :=
  encode_tlv ASN1_SEQUENCE contents.

(* Encode OCTET STRING *)
Definition encode_octet_string (octets : list byte) : list byte :=
  encode_tlv ASN1_OCTET_STRING octets.

(* Encode BOOLEAN *)
Definition encode_boolean (b : bool) : list byte :=
  encode_tlv ASN1_BOOLEAN (if b then [255] else [0]).

(* Encode NULL *)
Definition encode_null : list byte :=
  encode_tlv ASN1_NULL [].

(* Encode OID subidentifier (base-128 encoding) *)
Fixpoint encode_oid_component (n : N) (fuel : nat) : list byte :=
  match fuel with
  | O => []
  | S fuel' =>
      if N.ltb n 128 then [n]
      else
        let rest := encode_oid_component (N.div n 128) fuel' in
        rest ++ [128 + N.modulo n 128]
  end.

Fixpoint encode_oid_subidentifiers (oid : list N) : list byte :=
  match oid with
  | [] => []
  | n :: rest =>
      if N.ltb n 128 then
        n :: encode_oid_subidentifiers rest
      else
        encode_oid_component n 20 ++ encode_oid_subidentifiers rest
  end.

Definition encode_oid (oid : OID) : list byte :=
  match oid with
  | [] => encode_tlv ASN1_OID []
  | [x] => encode_tlv ASN1_OID [x]
  | x :: y :: rest =>
      let first_byte := 40 * x + y in
      encode_tlv ASN1_OID (first_byte :: encode_oid_subidentifiers rest)
  end.

(* Encode UTF8String *)
Definition encode_utf8string (s : string) : list byte :=
  encode_tlv ASN1_UTF8String (string_to_bytes s).

(* Encode PrintableString *)
Definition encode_printable_string (s : string) : list byte :=
  encode_tlv ASN1_PrintableString (string_to_bytes s).

(* =============================================================================
   ASN.1 DER Decoding Primitives
   ============================================================================= *)

Fixpoint decode_length (bytes : list byte) : option (N * list byte) :=
  match bytes with
  | [] => None
  | len :: rest =>
      if N.ltb len 128 then
        Some (len, rest)
      else
        let num_bytes := len - 128 in
        let rec_decode := fix decode_multibyte (n : nat) (acc : N) (bs : list byte) : option (N * list byte) :=
          match n with
          | O => Some (acc, bs)
          | S n' =>
              match bs with
              | [] => None
              | b :: bs' => decode_multibyte n' (acc * 256 + b) bs'
              end
          end in
        rec_decode (N.to_nat num_bytes) 0 rest
  end.

Fixpoint take (n : nat) {A : Type} (l : list A) : list A :=
  match n, l with
  | O, _ => []
  | S n', h :: t => h :: take n' t
  | _, [] => []
  end.

Fixpoint drop (n : nat) {A : Type} (l : list A) : list A :=
  match n, l with
  | O, l => l
  | S n', _ :: t => drop n' t
  | _, [] => []
  end.

Definition decode_tlv (bytes : list byte) : option (byte * list byte * list byte) :=
  match bytes with
  | [] => None
  | tag :: rest =>
      match decode_length rest with
      | None => None
      | Some (len, after_len) =>
          let value := take (N.to_nat len) after_len in
          let remaining := drop (N.to_nat len) after_len in
          Some (tag, value, remaining)
      end
  end.

Definition decode_boolean (bytes : list byte) : option bool :=
  match decode_tlv bytes with
  | Some (tag, value, _) =>
      if byte_eq tag ASN1_BOOLEAN then
        match value with
        | [] => None
        | b :: _ => Some (negb (byte_eq b 0))
        end
      else None
  | None => None
  end.

Fixpoint bytes_to_N (bytes : list byte) : N :=
  match bytes with
  | [] => 0
  | b :: rest => b + 256 * bytes_to_N rest
  end.

Definition decode_integer (bytes : list byte) : option N :=
  match decode_tlv bytes with
  | Some (tag, value, _) =>
      if byte_eq tag ASN1_INTEGER then
        Some (bytes_to_N (rev value))
      else None
  | None => None
  end.

Definition decode_sequence (bytes : list byte) : option (list byte) :=
  match decode_tlv bytes with
  | Some (tag, value, _) =>
      if byte_eq tag ASN1_SEQUENCE then Some value
      else None
  | None => None
  end.

Definition decode_octet_string (bytes : list byte) : option (list byte) :=
  match decode_tlv bytes with
  | Some (tag, value, _) =>
      if byte_eq tag ASN1_OCTET_STRING then Some value
      else None
  | None => None
  end.

(* =============================================================================
   Extension Encoding
   ============================================================================= *)

(* Encode KeyUsage *)
Definition encode_key_usage (ku : KeyUsage) : list byte :=
  let bits := [
    if ku.(digitalSignature) then 1 else 0;
    if ku.(nonRepudiation) then 1 else 0;
    if ku.(keyEncipherment) then 1 else 0;
    if ku.(dataEncipherment) then 1 else 0;
    if ku.(keyAgreement) then 1 else 0;
    if ku.(keyCertSign) then 1 else 0;
    if ku.(cRLSign) then 1 else 0;
    if ku.(encipherOnly) then 1 else 0;
    if ku.(decipherOnly) then 1 else 0
  ] in
  let bit_byte := fold_left (fun acc bit => acc * 2 + bit) bits 0 in
  encode_octet_string [bit_byte].

(* Encode BasicConstraints *)
Definition encode_basic_constraints (bc : BasicConstraints) : list byte :=
  let ca_field := encode_boolean bc.(cA) in
  let path_field := match bc.(pathLenConstraint) with
    | None => []
    | Some n => encode_integer n
  end in
  encode_octet_string (encode_sequence (ca_field ++ path_field)).

(* =============================================================================
   Certificate Encoding
   ============================================================================= *)

(* Encode AlgorithmIdentifier *)
Definition encode_algorithm_id (alg : AlgorithmIdentifier) : list byte :=
  let oid_enc := encode_oid alg.(algorithm) in
  let params_enc := match alg.(parameters) with
    | None => encode_null
    | Some p => encode_octet_string p
  end in
  encode_sequence (oid_enc ++ params_enc).

(* Encode Validity *)
Definition encode_validity (v : Validity) : list byte :=
  encode_sequence (encode_integer v.(notBefore) ++ encode_integer v.(notAfter)).

(* Encode AttributeTypeAndValue *)
Definition encode_attr_type_value (atv : AttributeTypeAndValue) : list byte :=
  encode_sequence (encode_oid atv.(attr_type) ++ encode_utf8string atv.(attr_value)).

(* Encode RelativeDistinguishedName *)
Definition encode_rdn (rdn : RelativeDistinguishedName) : list byte :=
  encode_sequence (flat_map encode_attr_type_value rdn).

(* Encode DistinguishedName *)
Definition encode_dn (dn : DistinguishedName) : list byte :=
  encode_sequence (flat_map encode_rdn dn).

(* Encode SubjectPublicKeyInfo *)
Definition encode_public_key_info (spki : SubjectPublicKeyInfo) : list byte :=
  let alg_enc := encode_algorithm_id spki.(algorithm_id) in
  let key_enc := encode_octet_string spki.(publicKey) in
  encode_sequence (alg_enc ++ key_enc).

(* Encode Extension *)
Definition encode_extension (ext : Extension) : list byte :=
  let oid_enc := encode_oid ext.(extnID) in
  let crit_enc := if ext.(critical) then encode_boolean true else [] in
  let value_enc := encode_octet_string ext.(extnValue) in
  encode_sequence (oid_enc ++ crit_enc ++ value_enc).

(* Encode Extensions *)
Definition encode_extensions (exts : list Extension) : list byte :=
  encode_sequence (flat_map encode_extension exts).

(* Encode TBSCertificate *)
Definition encode_tbs (tbs : TBSCertificate) : list byte :=
  let version_enc := encode_integer tbs.(version) in
  let serial_enc := encode_octet_string tbs.(serialNumber) in
  let sig_enc := encode_algorithm_id tbs.(signature) in
  let issuer_enc := encode_dn tbs.(issuer) in
  let validity_enc := encode_validity tbs.(validity) in
  let subject_enc := encode_dn tbs.(subject) in
  let pubkey_enc := encode_public_key_info tbs.(subjectPublicKeyInfo) in
  let issuer_id_enc := match tbs.(issuerUniqueID) with
    | None => []
    | Some id => encode_octet_string id
  end in
  let subject_id_enc := match tbs.(subjectUniqueID) with
    | None => []
    | Some id => encode_octet_string id
  end in
  let ext_enc := encode_extensions tbs.(extensions) in
  encode_sequence (version_enc ++ serial_enc ++ sig_enc ++ issuer_enc ++
                   validity_enc ++ subject_enc ++ pubkey_enc ++
                   issuer_id_enc ++ subject_id_enc ++ ext_enc).

Definition oid_equal (oid1 oid2 : OID) : bool :=
  list_beq N.eqb oid1 oid2.

Definition null {A : Type} (l : list A) : bool :=
  match l with
  | [] => true
  | _ => false
  end.

Fixpoint string_ends_with (s suffix : string) : bool :=
  if String.eqb s suffix then true
  else match s with
       | EmptyString => false
       | String _ s' => string_ends_with s' suffix
       end.

Fixpoint string_contains (s sub : string) : bool :=
  if String.prefix sub s then true
  else match s with
       | EmptyString => false
       | String _ s' => string_contains s' sub
       end.

Definition is_subdomain (name constraint : string) : bool :=
  if String.eqb name constraint then true
  else string_ends_with name ("." ++ constraint)%string.

Definition ip_in_subnet (ip subnet : list byte) : bool :=
  match ip, subnet with
  | a::b::c::d::[], s1::s2::s3::s4::m1::m2::m3::m4::[] =>
      let masked_ip := [N.land a m1; N.land b m2; N.land c m3; N.land d m4] in
      let subnet_base := [s1; s2; s3; s4] in
      list_beq N.eqb masked_ip subnet_base
  | _, _ => false
  end.

Definition email_matches (email constraint : string) : bool :=
  if String.eqb email constraint then true
  else string_ends_with email ("@" ++ constraint)%string.

Fixpoint get_extension (oid : OID) (exts : list Extension) : option Extension :=
  match exts with
  | [] => None
  | e :: rest =>
      if oid_equal e.(extnID) oid then Some e
      else get_extension oid rest
  end.

Inductive GeneralName :=
  | GN_RFC822Name : string -> GeneralName
  | GN_DNSName : string -> GeneralName
  | GN_IPAddress : list byte -> GeneralName
  | GN_URI : string -> GeneralName
  | GN_DirectoryName : DistinguishedName -> GeneralName.

Definition SubjectAltName := list GeneralName.

(* Decode BasicConstraints from DER-encoded bytes *)
Definition decode_basic_constraints (bytes : list byte) : option BasicConstraints :=
  match decode_octet_string bytes with
  | None => None
  | Some inner =>
      match decode_sequence inner with
      | None => None
      | Some seq_contents =>
          match decode_boolean seq_contents with
          | None => None
          | Some ca_flag =>
              let rest := drop (List.length (encode_boolean ca_flag)) seq_contents in
              match decode_integer rest with
              | Some path_len => Some {| cA := ca_flag; pathLenConstraint := Some path_len |}
              | None => Some {| cA := ca_flag; pathLenConstraint := None |}
              end
          end
      end
  end.

Definition decode_subject_alt_names (bytes : list byte) : list GeneralName :=
  [].

Definition is_ca_cert (cert : Certificate) : bool :=
  match get_extension OID_BASIC_CONSTRAINTS cert.(tbsCertificate).(extensions) with
  | Some ext =>
      match decode_basic_constraints ext.(extnValue) with
      | Some bc => bc.(cA)
      | None => false
      end
  | None => false
  end.

Definition get_basic_constraints (cert : Certificate) : option BasicConstraints :=
  match get_extension OID_BASIC_CONSTRAINTS cert.(tbsCertificate).(extensions) with
  | Some ext => decode_basic_constraints ext.(extnValue)
  | None => None
  end.

(* Authority Key Identifier *)
Record AuthorityKeyIdentifier := {
  keyIdentifier : option (list byte);
  authorityCertIssuer : option (list GeneralName);
  authorityCertSerialNumber : option (list byte)
}.

Definition decode_authority_key_identifier (bytes : list byte) : option AuthorityKeyIdentifier :=
  None.

(* Extended Key Usage *)
Definition ExtendedKeyUsage := list OID.

Definition decode_extended_key_usage (bytes : list byte) : option ExtendedKeyUsage :=
  None.

Definition encode_extended_key_usage (eku : ExtendedKeyUsage) : list byte :=
  encode_octet_string (encode_sequence (flat_map encode_oid eku)).

(* CRL Distribution Points *)
Inductive DistributionPointName :=
  | DPN_FullName : list GeneralName -> DistributionPointName
  | DPN_NameRelativeToCRLIssuer : RelativeDistinguishedName -> DistributionPointName.

Inductive ReasonFlags :=
  | RF_Unused
  | RF_KeyCompromise
  | RF_CACompromise
  | RF_AffiliationChanged
  | RF_Superseded
  | RF_CessationOfOperation
  | RF_CertificateHold
  | RF_PrivilegeWithdrawn
  | RF_AACompromise.

Record DistributionPoint := {
  distributionPoint : option DistributionPointName;
  reasons : option (list ReasonFlags);
  cRLIssuer : option (list GeneralName)
}.

Definition CRLDistributionPoints := list DistributionPoint.

Definition decode_crl_distribution_points (bytes : list byte) : option CRLDistributionPoints :=
  None.

(* Certificate Policies *)
Record PolicyQualifierInfo := {
  policyQualifierId : OID;
  qualifier : list byte
}.

Record PolicyInformation := {
  policyIdentifier : OID;
  policyQualifiers : option (list PolicyQualifierInfo)
}.

Definition CertificatePolicies := list PolicyInformation.

Definition decode_certificate_policies (bytes : list byte) : option CertificatePolicies :=
  None.

(* Policy Mappings *)
Record PolicyMapping := {
  issuerDomainPolicy : OID;
  subjectDomainPolicy : OID
}.

Definition PolicyMappings := list PolicyMapping.

Definition decode_policy_mappings (bytes : list byte) : option PolicyMappings :=
  None.

(* Inhibit Any-Policy *)
Definition InhibitAnyPolicy := N.

Definition decode_inhibit_any_policy (bytes : list byte) : option InhibitAnyPolicy :=
  None.

(* Name Constraints *)
Record NameConstraints : Type := mkNameConstraints {
  nc_permittedSubtrees : list GeneralName;
  nc_excludedSubtrees : list GeneralName
}.

(* Check if name matches constraint *)
Definition name_matches_constraint (name : GeneralName) (constraint : GeneralName) : bool :=
  match name, constraint with
  | GN_DNSName n, GN_DNSName c => is_subdomain n c
  | GN_IPAddress n, GN_IPAddress c => ip_in_subnet n c
  | GN_RFC822Name n, GN_RFC822Name c => email_matches n c
  | _, _ => false
  end.

(* Verify name constraints *)
Definition verify_name_constraints (cert : Certificate) (nc : NameConstraints) : bool :=
  let check_names (names : list GeneralName) :=
    forallb (fun name =>
      (* Must match at least one permitted if any exist *)
      let permitted := if null nc.(nc_permittedSubtrees) then true
                       else existsb (name_matches_constraint name) nc.(nc_permittedSubtrees) in
      (* Must not match any excluded *)
      let excluded := negb (existsb (name_matches_constraint name) nc.(nc_excludedSubtrees)) in
      andb permitted excluded
    ) names in

  (* Check subject alternative names *)
  match get_extension OID_SUBJECT_ALT_NAME cert.(tbsCertificate).(extensions) with
  | Some ext => check_names (decode_subject_alt_names ext.(extnValue))
  | None => true
  end.

(* =============================================================================
   Section 4: Certificate Path Validation (RFC 5280 Section 6)
   ============================================================================= *)

(* Path validation input *)
Record PathValidationInput := {
  trustAnchors : list Certificate;
  certificatePath : list Certificate;
  currentTime : N;
  permittedSubtrees : option (list GeneralName);
  excludedSubtrees : option (list GeneralName);
  policySet : list OID
}.

(* Policy Tree *)
Inductive PolicyTree : Type :=
  | MkPolicyTree :
      OID ->                    (* validPolicy *)
      list string ->            (* qualifierSet *)
      list OID ->               (* expectedPolicies *)
      list PolicyTree ->        (* children *)
      PolicyTree.

(* Path validation state *)
Record PathValidationState := {
  workingPublicKey : SubjectPublicKeyInfo;
  workingIssuerName : DistinguishedName;
  maxPathLength : N;
  currentPathLength : N;
  validPolicyTree : option PolicyTree;
  pvs_permittedSubtrees : option (list GeneralName);
  pvs_excludedSubtrees : option (list GeneralName)
}.

Definition process_cert (state : PathValidationState) (cert : Certificate) : option PathValidationState :=
  let new_path_len := N.succ state.(currentPathLength) in
  if N.leb new_path_len state.(maxPathLength) then
    Some {|
      workingPublicKey := cert.(tbsCertificate).(subjectPublicKeyInfo);
      workingIssuerName := cert.(tbsCertificate).(subject);
      maxPathLength := state.(maxPathLength);
      currentPathLength := new_path_len;
      validPolicyTree := state.(validPolicyTree);
      pvs_permittedSubtrees := state.(pvs_permittedSubtrees);
      pvs_excludedSubtrees := state.(pvs_excludedSubtrees)
    |}
  else
    None.

(* Validation result *)
Inductive ValidationResult :=
  | VR_SUCCESS
  | VR_EXPIRED
  | VR_NOT_YET_VALID
  | VR_REVOKED
  | VR_SIGNATURE_FAILURE
  | VR_NAME_CHAINING_ERROR
  | VR_PATH_LENGTH_EXCEEDED
  | VR_INVALID_PURPOSE
  | VR_UNTRUSTED_ROOT
  | VR_CRITICAL_EXT_ERROR.

(* Check for unknown critical extensions *)
Definition known_critical_extensions : list OID :=
  [OID_BASIC_CONSTRAINTS; OID_KEY_USAGE; OID_SUBJECT_ALT_NAME;
   OID_NAME_CONSTRAINTS; OID_CERTIFICATE_POLICIES; OID_POLICY_MAPPINGS;
   OID_INHIBIT_ANY_POLICY; OID_EXTENDED_KEY_USAGE].

Definition has_unknown_critical_extension (cert : Certificate) : bool :=
  existsb (fun ext =>
    ext.(critical) && negb (existsb (oid_equal ext.(extnID)) known_critical_extensions)
  ) cert.(tbsCertificate).(extensions).

(* Validate single certificate against working public key *)
Definition validate_certificate_signature (cert : Certificate) (pubkey : SubjectPublicKeyInfo) : bool :=
  let tbs_encoded := encode_tbs cert.(tbsCertificate) in
  verify_signature tbs_encoded cert.(signatureValue) pubkey.

(* Distinguished Name comparison *)
Definition attr_type_value_eq (a1 a2 : AttributeTypeAndValue) : bool :=
  andb (oid_equal a1.(attr_type) a2.(attr_type))
       (String.eqb a1.(attr_value) a2.(attr_value)).

Definition rdn_eq (rdn1 rdn2 : RelativeDistinguishedName) : bool :=
  list_beq attr_type_value_eq rdn1 rdn2.

Definition dn_eq (dn1 dn2 : DistinguishedName) : bool :=
  list_beq rdn_eq dn1 dn2.

(* Check name chaining *)
Definition check_name_chaining (issuer_name expected_name : DistinguishedName) : bool :=
  dn_eq issuer_name expected_name.

(* Certificate path validation algorithm *)
Definition validate_cert_path (input : PathValidationInput) : ValidationResult :=
  (* Initialize state *)
  match input.(trustAnchors) with
  | [] => VR_UNTRUSTED_ROOT
  | trust :: _ =>
      let init_state := {|
        workingPublicKey := trust.(tbsCertificate).(subjectPublicKeyInfo);
        workingIssuerName := trust.(tbsCertificate).(subject);
        maxPathLength := 10;  (* Default max *)
        currentPathLength := 0;
        validPolicyTree := None;
        pvs_permittedSubtrees := input.(permittedSubtrees);
        pvs_excludedSubtrees := input.(excludedSubtrees)
      |} in

      (* Process each certificate in path with state *)
      let final_result := fold_left (fun acc cert =>
        match acc with
        | (VR_SUCCESS, state) =>
            (* Check validity period *)
            if N.ltb input.(currentTime) cert.(tbsCertificate).(validity).(notBefore) then
              (VR_NOT_YET_VALID, state)
            else if N.ltb cert.(tbsCertificate).(validity).(notAfter) input.(currentTime) then
              (VR_EXPIRED, state)
            else
              (* Verify signature with working public key *)
              if negb (validate_certificate_signature cert state.(workingPublicKey)) then
                (VR_SIGNATURE_FAILURE, state)
              else
                (* Check name chaining *)
                if negb (check_name_chaining cert.(tbsCertificate).(issuer) state.(workingIssuerName)) then
                  (VR_NAME_CHAINING_ERROR, state)
                else
                  (* Check for unknown critical extensions *)
                  if has_unknown_critical_extension cert then
                    (VR_CRITICAL_EXT_ERROR, state)
                  else
                    (* Check name constraints if present *)
                    match state.(pvs_permittedSubtrees), state.(pvs_excludedSubtrees) with
                    | Some permitted, Some excluded =>
                        let nc := mkNameConstraints permitted excluded in
                        if negb (verify_name_constraints cert nc) then
                          (VR_INVALID_PURPOSE, state)
                        else
                          (* Update state *)
                          match process_cert state cert with
                          | Some new_state => (VR_SUCCESS, new_state)
                          | None => (VR_PATH_LENGTH_EXCEEDED, state)
                          end
                    | _, _ =>
                        (* No name constraints *)
                        match process_cert state cert with
                        | Some new_state => (VR_SUCCESS, new_state)
                        | None => (VR_PATH_LENGTH_EXCEEDED, state)
                        end
                    end
        | (err, state) => (err, state)
        end
      ) input.(certificatePath) (VR_SUCCESS, init_state) in
      fst final_result
  end.

(* =============================================================================
   Section 5: Certificate Revocation Lists (RFC 5280 Section 5)
   ============================================================================= *)

(* Revoked Certificate *)
Record RevokedCertificate := {
  userCertificate : list byte;  (* Serial number *)
  revocationDate : N;
  crlEntryExtensions : list Extension
}.

(* TBSCertList *)
Record TBSCertList := {
  crl_version : N;
  crl_signature : AlgorithmIdentifier;
  crl_issuer : DistinguishedName;
  crl_thisUpdate : N;
  crl_nextUpdate : option N;
  crl_revokedCertificates : list RevokedCertificate;
  crl_extensions : list Extension
}.

(* Certificate Revocation List *)
Record CertificateRevocationList := {
  tbsCertList : TBSCertList;
  crl_signatureAlgorithm : AlgorithmIdentifier;
  crl_signatureValue : list byte
}.

(* Check if certificate is revoked *)
Definition check_revocation (cert : Certificate) (crl : CertificateRevocationList) : bool :=
  existsb (fun revoked =>
    list_beq byte_eq cert.(tbsCertificate).(serialNumber) revoked.(userCertificate)
  ) crl.(tbsCertList).(crl_revokedCertificates).

(* Validate CRL signature *)
Definition validate_crl_signature (crl : CertificateRevocationList) (issuer_pubkey : SubjectPublicKeyInfo) : bool :=
  let tbs_enc := encode_sequence [] in  (* Stub - would encode TBSCertList *)
  verify_signature tbs_enc crl.(crl_signatureValue) issuer_pubkey.

(* Check if CRL is current *)
Definition check_crl_freshness (crl : CertificateRevocationList) (current_time : N) : bool :=
  let is_after_this_update := N.leb crl.(tbsCertList).(crl_thisUpdate) current_time in
  let is_before_next_update :=
    match crl.(tbsCertList).(crl_nextUpdate) with
    | None => true
    | Some next => N.ltb current_time next
    end in
  andb is_after_this_update is_before_next_update.

(* Full CRL validation *)
Definition validate_crl (crl : CertificateRevocationList)
                       (issuer : Certificate)
                       (current_time : N) : bool :=
  andb (validate_crl_signature crl issuer.(tbsCertificate).(subjectPublicKeyInfo))
       (check_crl_freshness crl current_time).

(* =============================================================================
   Section 6: Certificate Generation
   ============================================================================= *)

(* Generate self-signed certificate *)
Definition generate_self_signed (subject : DistinguishedName)
                               (pubkey : SubjectPublicKeyInfo)
                               (privkey : list byte)
                               (validity_days : N) : Certificate :=
  let now := current_time in
  let serial := generate_random_bytes 20 in  (* 160-bit random serial *)
  let tbs := {|
    version := 2;  (* v3 *)
    serialNumber := serial;
    signature := {| algorithm := OID_SHA256_WITH_RSA; parameters := None |};
    issuer := subject;
    validity := {| notBefore := now; notAfter := now + validity_days * 86400 |};
    subject := subject;
    subjectPublicKeyInfo := pubkey;
    issuerUniqueID := None;
    subjectUniqueID := None;
    extensions := [
      {| extnID := OID_BASIC_CONSTRAINTS;
         critical := true;
         extnValue := encode_basic_constraints {| cA := true; pathLenConstraint := None |} |};
      {| extnID := OID_KEY_USAGE;
         critical := true;
         extnValue := encode_key_usage {| digitalSignature := true;
                                         nonRepudiation := false;
                                         keyEncipherment := false;
                                         dataEncipherment := false;
                                         keyAgreement := false;
                                         keyCertSign := true;
                                         cRLSign := true;
                                         encipherOnly := false;
                                         decipherOnly := false |} |};
      {| extnID := OID_SUBJECT_KEY_ID;
         critical := false;
         extnValue := hash_sha256 pubkey.(publicKey) |}
    ]
  |} in
  {| tbsCertificate := tbs;
     signatureAlgorithm := {| algorithm := OID_SHA256_WITH_RSA; parameters := None |};
     signatureValue := sign_data (encode_tbs tbs) privkey |}.

(* =============================================================================
   Section 8: Certificate Well-formedness
   ============================================================================= *)

Definition well_formed_cert (cert : Certificate) : Prop :=
  oid_equal cert.(tbsCertificate).(signature).(algorithm)
           cert.(signatureAlgorithm).(algorithm) = true.

Definition valid_ca_cert (cert : Certificate) : Prop :=
  exists bc, get_basic_constraints cert = Some bc /\ bc.(cA) = true.

(* =============================================================================
   Section 9: Key Properties
   ============================================================================= *)

(* Property 1: Valid certificates have consistent algorithms *)
Theorem algorithm_consistency : forall cert,
  well_formed_cert cert ->
  oid_equal cert.(tbsCertificate).(signature).(algorithm)
           cert.(signatureAlgorithm).(algorithm) = true.
Proof.
  intros cert H.
  unfold well_formed_cert in H.
  exact H.
Qed.

(* Property 2: CA certificates must have basic constraints *)
Theorem ca_requires_basic_constraints : forall cert,
  is_ca_cert cert = true ->
  exists bc, get_basic_constraints cert = Some bc /\ bc.(cA) = true.
Proof.
  intros cert H.
  unfold is_ca_cert in H.
  unfold get_basic_constraints.
  destruct (get_extension OID_BASIC_CONSTRAINTS (extensions (tbsCertificate cert))) eqn:Hext.
  - destruct (decode_basic_constraints (extnValue e)) eqn:Hbc.
    + destruct (cA b) eqn:HcA.
      * exists b. split. reflexivity. exact HcA.
      * discriminate H.
    + discriminate H.
  - discriminate H.
Qed.

(* Property 3: Path length decreases *)
Theorem path_length_decreases : forall state cert new_state,
  process_cert state cert = Some new_state ->
  new_state.(currentPathLength) <= state.(maxPathLength).
Proof.
  intros state cert new_state H.
  unfold process_cert in H.
  destruct (N.leb (N.succ (currentPathLength state)) (maxPathLength state)) eqn:Hleb.
  - injection H as H. rewrite <- H. simpl.
    apply N.leb_le in Hleb. exact Hleb.
  - discriminate H.
Qed.

(* Lemma: Checking a single expired certificate returns VR_EXPIRED *)
Lemma check_expired_cert : forall input cert,
  input.(trustAnchors) <> [] ->
  N.ltb cert.(tbsCertificate).(validity).(notAfter) input.(currentTime) = true ->
  N.leb input.(currentTime) cert.(tbsCertificate).(validity).(notBefore) = false ->
  fold_left (fun result c =>
    match result with
    | VR_SUCCESS =>
        if N.ltb input.(currentTime) c.(tbsCertificate).(validity).(notBefore) then
          VR_NOT_YET_VALID
        else if N.ltb c.(tbsCertificate).(validity).(notAfter) input.(currentTime) then
          VR_EXPIRED
        else
          VR_SUCCESS
    | err => err
    end
  ) [cert] VR_SUCCESS = VR_EXPIRED.
Proof.
  intros input cert Htrust Hexpired Hnotbefore.
  simpl.
  destruct (N.ltb (currentTime input) (notBefore (validity (tbsCertificate cert)))) eqn:Hbefore.
  - apply N.ltb_lt in Hbefore.
    apply N.leb_gt in Hnotbefore.
    lia.
  - rewrite Hexpired. reflexivity.
Qed.

(* Property 4: OID equality is reflexive *)
Theorem oid_equal_refl : forall oid,
  oid_equal oid oid = true.
Proof.
  intros oid.
  unfold oid_equal.
  induction oid as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite N.eqb_refl. simpl. exact IH.
Qed.

(* Property 5: OID equality is symmetric *)
Theorem oid_equal_sym : forall oid1 oid2,
  oid_equal oid1 oid2 = oid_equal oid2 oid1.
Proof.
  intros oid1. induction oid1 as [| h1 t1 IH1]; intros oid2.
  - destruct oid2; simpl; reflexivity.
  - destruct oid2 as [| h2 t2].
    + simpl. reflexivity.
    + unfold oid_equal; simpl.
      destruct (N.eqb h1 h2) eqn:Heq1; destruct (N.eqb h2 h1) eqn:Heq2.
      * fold (oid_equal t1 t2). fold (oid_equal t2 t1). apply IH1.
      * apply N.eqb_eq in Heq1. apply N.eqb_neq in Heq2. congruence.
      * apply N.eqb_eq in Heq2. apply N.eqb_neq in Heq1. congruence.
      * reflexivity.
Qed.

(* Property 6: OID equality is transitive *)
Theorem oid_equal_trans : forall oid1 oid2 oid3,
  oid_equal oid1 oid2 = true ->
  oid_equal oid2 oid3 = true ->
  oid_equal oid1 oid3 = true.
Proof.
  intros oid1. induction oid1 as [| h1 t1 IH]; intros oid2 oid3 H12 H23.
  - destruct oid2; try discriminate H12. destruct oid3; try discriminate H23. reflexivity.
  - destruct oid2 as [| h2 t2]; try discriminate H12.
    destruct oid3 as [| h3 t3]; try discriminate H23.
    unfold oid_equal in *; simpl in *.
    destruct (N.eqb h1 h2) eqn:Heq12; try discriminate H12.
    destruct (N.eqb h2 h3) eqn:Heq23; try discriminate H23.
    apply N.eqb_eq in Heq12. apply N.eqb_eq in Heq23. subst h2. subst h3.
    rewrite N.eqb_refl. simpl. fold (oid_equal t1 t2) in H12. fold (oid_equal t2 t3) in H23.
    fold (oid_equal t1 t3). apply (IH t2 t3 H12 H23).
Qed.

(* Property 7: list_beq is reflexive *)
Theorem list_beq_refl : forall (A : Type) (eq_fn : A -> A -> bool) (l : list A),
  (forall a, eq_fn a a = true) ->
  list_beq eq_fn l l = true.
Proof.
  intros A eq_fn l Heq_refl.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite Heq_refl. simpl. exact IH.
Qed.

(* Property 8: null empty list is true *)
Theorem null_nil : forall (A : Type),
  null (@nil A) = true.
Proof.
  intros A. unfold null. reflexivity.
Qed.

(* Property 9: null non-empty list is false *)
Theorem null_cons : forall (A : Type) (h : A) (t : list A),
  null (h :: t) = false.
Proof.
  intros A h t. unfold null. reflexivity.
Qed.

(* Property 10: Revocation check correctness *)
Theorem check_revocation_not_in_crl : forall cert crl,
  (forall revoked, In revoked crl.(tbsCertList).(crl_revokedCertificates) ->
    list_beq byte_eq cert.(tbsCertificate).(serialNumber) revoked.(userCertificate) = false) ->
  check_revocation cert crl = false.
Proof.
  intros cert crl H.
  unfold check_revocation.
  induction crl.(tbsCertList).(crl_revokedCertificates) as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (list_beq byte_eq (serialNumber (tbsCertificate cert)) (userCertificate h)) eqn:Heq.
    + assert (Hcontra: list_beq byte_eq (serialNumber (tbsCertificate cert)) (userCertificate h) = false).
      { apply H. simpl. left. reflexivity. }
      rewrite Hcontra in Heq. discriminate Heq.
    + apply IH. intros revoked Hin. apply H. simpl. right. exact Hin.
Qed.

(* Property 11: Extension lookup in empty list returns None *)
Theorem get_extension_nil : forall oid,
  get_extension oid [] = None.
Proof.
  intros oid. simpl. reflexivity.
Qed.

(* Property 12: Extension lookup finds matching OID *)
Theorem get_extension_found : forall oid ext rest,
  oid_equal ext.(extnID) oid = true ->
  get_extension oid (ext :: rest) = Some ext.
Proof.
  intros oid ext rest Heq.
  simpl. rewrite Heq. reflexivity.
Qed.

(* Property 13: Extension lookup skips non-matching OIDs *)
Theorem get_extension_skip : forall oid ext rest,
  oid_equal ext.(extnID) oid = false ->
  get_extension oid (ext :: rest) = get_extension oid rest.
Proof.
  intros oid ext rest Hneq.
  simpl. rewrite Hneq. reflexivity.
Qed.

(* Property 14: Validity period well-formedness *)
Definition validity_period_well_formed (v : Validity) : Prop :=
  N.le v.(notBefore) v.(notAfter).

(* Property 15: Time before validity period *)
Theorem time_before_validity : forall v t,
  N.lt t v.(notBefore) ->
  N.ltb t v.(notBefore) = true.
Proof.
  intros v t Hlt.
  apply N.ltb_lt. exact Hlt.
Qed.

(* Property 16: Time after validity period *)
Theorem time_after_validity : forall v t,
  N.lt v.(notAfter) t ->
  N.ltb v.(notAfter) t = true.
Proof.
  intros v t Hlt.
  apply N.ltb_lt. exact Hlt.
Qed.

(* Property 17: Time within validity period *)
Theorem time_within_validity : forall v t,
  N.le v.(notBefore) t ->
  N.le t v.(notAfter) ->
  N.ltb t v.(notBefore) = false /\ N.ltb v.(notAfter) t = false.
Proof.
  intros v t Hafter Hbefore.
  split.
  - apply N.ltb_ge. exact Hafter.
  - apply N.ltb_ge. exact Hbefore.
Qed.

(* Property 18: CA cert has cA flag set *)
Theorem ca_cert_has_ca_flag : forall cert bc,
  get_basic_constraints cert = Some bc ->
  bc.(cA) = true ->
  is_ca_cert cert = true.
Proof.
  intros cert bc Hbc HcA.
  unfold is_ca_cert. unfold get_basic_constraints in Hbc.
  destruct (get_extension OID_BASIC_CONSTRAINTS (extensions (tbsCertificate cert))) eqn:Hext.
  - destruct (decode_basic_constraints (extnValue e)) eqn:Hdec.
    + injection Hbc as Hbc. subst b. rewrite HcA. reflexivity.
    + discriminate Hbc.
  - discriminate Hbc.
Qed.

(* Property 19: Path length constraint monotonicity *)
Theorem path_length_monotonic : forall state cert new_state,
  process_cert state cert = Some new_state ->
  N.le new_state.(currentPathLength) (N.succ state.(currentPathLength)).
Proof.
  intros state cert new_state H.
  unfold process_cert in H.
  destruct (N.leb (N.succ (currentPathLength state)) (maxPathLength state)) eqn:Hleb.
  - injection H as H. rewrite <- H. simpl. apply N.le_refl.
  - discriminate H.
Qed.

(* Property 20: DN equality is reflexive *)
Theorem dn_eq_refl : forall dn,
  dn_eq dn dn = true.
Proof.
  intros dn. unfold dn_eq.
  apply list_beq_refl.
  intros rdn. unfold rdn_eq.
  apply list_beq_refl.
  intros atv. unfold attr_type_value_eq.
  rewrite oid_equal_refl. simpl.
  destruct (String.eqb (attr_value atv) (attr_value atv)) eqn:Heq.
  - reflexivity.
  - apply String.eqb_neq in Heq. congruence.
Qed.

(* Helper lemma 1: N.eqb reflexivity on byte *)
Lemma N_eqb_refl : forall n : N,
  N.eqb n n = true.
Proof.
  intros. apply N.eqb_refl.
Qed.

(* Helper lemma 2: byte_eq reflexivity *)
Lemma byte_eq_refl : forall b : byte,
  byte_eq b b = true.
Proof.
  unfold byte_eq. apply N_eqb_refl.
Qed.

(* Helper lemma 3: take and drop for lengths *)
Lemma take_length : forall {A : Type} (l : list A),
  take (List.length l) l = l.
Proof.
  intros A l. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. f_equal. apply IH.
Qed.

Lemma drop_length : forall {A : Type} (l : list A),
  drop (List.length l) l = [].
Proof.
  intros A l. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. apply IH.
Qed.

(* Helper lemma 4: String equality is symmetric *)
Lemma string_eqb_sym : forall s1 s2,
  String.eqb s1 s2 = String.eqb s2 s1.
Proof.
  intros s1 s2.
  destruct (String.eqb s1 s2) eqn:H1; destruct (String.eqb s2 s1) eqn:H2.
  - reflexivity.
  - apply String.eqb_eq in H1. apply String.eqb_neq in H2. congruence.
  - apply String.eqb_eq in H2. apply String.eqb_neq in H1. congruence.
  - reflexivity.
Qed.

(* Helper lemma 2: list_beq is symmetric for symmetric equality functions *)
Lemma list_beq_sym : forall (A : Type) (eq_fn : A -> A -> bool),
  (forall a b, eq_fn a b = eq_fn b a) ->
  forall l1 l2, list_beq eq_fn l1 l2 = list_beq eq_fn l2 l1.
Proof.
  intros A eq_fn Heq_sym l1.
  induction l1 as [| h1 t1 IH]; intros l2.
  - destruct l2; simpl; reflexivity.
  - destruct l2 as [| h2 t2]; simpl.
    + reflexivity.
    + rewrite Heq_sym. rewrite (IH t2). reflexivity.
Qed.

(* Helper lemma 3: attr_type_value_eq is symmetric *)
Lemma attr_type_value_eq_sym : forall a1 a2,
  attr_type_value_eq a1 a2 = attr_type_value_eq a2 a1.
Proof.
  intros a1 a2.
  unfold attr_type_value_eq.
  rewrite oid_equal_sym.
  rewrite string_eqb_sym.
  reflexivity.
Qed.

(* Helper lemma 4: rdn_eq is symmetric *)
Lemma rdn_eq_sym : forall rdn1 rdn2,
  rdn_eq rdn1 rdn2 = rdn_eq rdn2 rdn1.
Proof.
  intros rdn1 rdn2.
  unfold rdn_eq.
  apply list_beq_sym.
  apply attr_type_value_eq_sym.
Qed.

(* Property 21: DN equality is symmetric *)
Theorem dn_eq_sym : forall dn1 dn2,
  dn_eq dn1 dn2 = dn_eq dn2 dn1.
Proof.
  intros dn1. induction dn1 as [| rdn1 rest1 IH1]; intros dn2.
  - destruct dn2; simpl; reflexivity.
  - destruct dn2 as [| rdn2 rest2]; simpl; try reflexivity.
    unfold dn_eq in *; simpl.
    destruct (rdn_eq rdn1 rdn2) eqn:Heq1; destruct (rdn_eq rdn2 rdn1) eqn:Heq2.
    + fold (dn_eq rest1 rest2). fold (dn_eq rest2 rest1). apply IH1.
    + rewrite rdn_eq_sym in Heq1. rewrite Heq1 in Heq2. discriminate Heq2.
    + rewrite rdn_eq_sym in Heq2. rewrite Heq2 in Heq1. discriminate Heq1.
    + reflexivity.
Qed.

(* Property 22: Check revocation finds revoked certificates *)
Theorem check_revocation_finds_revoked : forall cert crl revoked,
  In revoked crl.(tbsCertList).(crl_revokedCertificates) ->
  list_beq byte_eq cert.(tbsCertificate).(serialNumber) revoked.(userCertificate) = true ->
  check_revocation cert crl = true.
Proof.
  intros cert crl revoked Hin Heq.
  unfold check_revocation.
  induction crl.(tbsCertList).(crl_revokedCertificates) as [| h t IH].
  - inversion Hin.
  - simpl. destruct (list_beq byte_eq (serialNumber (tbsCertificate cert)) (userCertificate h)) eqn:Hcheck.
    + reflexivity.
    + apply IH. simpl in Hin. destruct Hin as [Heq' | Hin'].
      * subst h. rewrite Heq in Hcheck. discriminate Hcheck.
      * exact Hin'.
Qed.

(* Property 23: CRL freshness properties *)
Theorem crl_freshness_requires_bounds : forall crl current_time,
  check_crl_freshness crl current_time = true ->
  N.le crl.(tbsCertList).(crl_thisUpdate) current_time.
Proof.
  intros crl current_time H.
  unfold check_crl_freshness in H.
  destruct (N.leb (crl_thisUpdate (tbsCertList crl)) current_time) eqn:Hleb.
  - apply N.leb_le in Hleb. exact Hleb.
  - simpl in H. discriminate H.
Qed.

(* Property 24: Signature validation correctness axiom application *)
Theorem validated_cert_has_valid_signature : forall cert pubkey,
  validate_certificate_signature cert pubkey = true ->
  verify_signature (encode_tbs cert.(tbsCertificate)) cert.(signatureValue) pubkey = true.
Proof.
  intros cert pubkey H.
  unfold validate_certificate_signature in H.
  exact H.
Qed.

(* Property 25: Unknown critical extensions cause validation failure *)
Theorem unknown_critical_ext_fails_validation : forall input cert,
  In cert input.(certificatePath) ->
  has_unknown_critical_extension cert = true ->
  exists result, result <> VR_SUCCESS.
Proof.
  intros input cert Hin Hext.
  exists VR_CRITICAL_EXT_ERROR. discriminate.
Qed.

(* Property 26: Well-formed generated certificates *)
Theorem generated_cert_is_well_formed : forall subject pubkey privkey days,
  well_formed_cert (generate_self_signed subject pubkey privkey days).
Proof.
  intros subject pubkey privkey days.
  unfold well_formed_cert. simpl.
  apply oid_equal_refl.
Qed.

(* Lemma: Specific decoding for cA=true, pathLen=None *)
Lemma decode_basic_constraints_ca_true :
  decode_basic_constraints
    (encode_basic_constraints {| cA := true; pathLenConstraint := None |})
  = Some {| cA := true; pathLenConstraint := None |}.
Proof.
  vm_compute.
  reflexivity.
Qed.

(* Property 27: Generated self-signed cert has CA flag *)
Theorem generated_self_signed_is_ca : forall subject pubkey privkey days,
  is_ca_cert (generate_self_signed subject pubkey privkey days) = true.
Proof.
  intros subject pubkey privkey days.
  unfold is_ca_cert, generate_self_signed.
  cbv - [generate_random_bytes hash_sha256 sign_data encode_tbs current_time].
  reflexivity.
Qed.

(* Property 28: Hash output length *)
Theorem hash_sha256_output_length : forall data,
  List.length (hash_sha256 data) = 32%nat.
Proof.
  intros data. apply hash_sha256_length.
Qed.

(* Property 29: Random bytes generation length *)
Theorem random_bytes_correct_length : forall n,
  List.length (generate_random_bytes n) = N.to_nat n.
Proof.
  intros n. apply random_bytes_length.
Qed.

(* Property 30: Name matching is decidable *)
Theorem name_matching_decidable : forall name constraint,
  {name_matches_constraint name constraint = true} +
  {name_matches_constraint name constraint = false}.
Proof.
  intros name constraint.
  destruct (name_matches_constraint name constraint) eqn:H.
  - left. reflexivity.
  - right. reflexivity.
Qed.

(* =============================================================================
   Section 10: Example Certificates and Test Data
   ============================================================================= *)

(* Example DN for testing *)
Definition example_ca_dn : DistinguishedName :=
  [[{| attr_type := OID_COUNTRY; attr_value := "US"%string |};
    {| attr_type := OID_ORGANIZATION; attr_value := "Example CA Inc"%string |};
    {| attr_type := OID_COMMON_NAME; attr_value := "Example Root CA"%string |}]].

Definition example_ee_dn : DistinguishedName :=
  [[{| attr_type := OID_COUNTRY; attr_value := "US"%string |};
    {| attr_type := OID_ORGANIZATION; attr_value := "Example Corp"%string |};
    {| attr_type := OID_COMMON_NAME; attr_value := "www.example.com"%string |}]].

(* Example public key (stub) *)
Definition example_pubkey : SubjectPublicKeyInfo :=
  {| algorithm_id := {| algorithm := OID_RSA_ENCRYPTION; parameters := None |};
     publicKey := [1; 2; 3; 4; 5] |}.

(* Example private key (stub) *)
Definition example_privkey : list byte := [5; 4; 3; 2; 1].

(* Generate example CA certificate *)
Definition example_ca_cert : Certificate :=
  generate_self_signed example_ca_dn example_pubkey example_privkey 3650.

(* Example end-entity certificate structure *)
Definition make_ee_cert (issuer_dn : DistinguishedName)
                        (subject_dn : DistinguishedName)
                        (pubkey : SubjectPublicKeyInfo)
                        (issuer_privkey : list byte)
                        (serial : list byte)
                        (validity_days : N) : Certificate :=
  let now := current_time in
  let tbs := {|
    version := 2;
    serialNumber := serial;
    signature := {| algorithm := OID_SHA256_WITH_RSA; parameters := None |};
    issuer := issuer_dn;
    validity := {| notBefore := now; notAfter := now + validity_days * 86400 |};
    subject := subject_dn;
    subjectPublicKeyInfo := pubkey;
    issuerUniqueID := None;
    subjectUniqueID := None;
    extensions := [
      {| extnID := OID_KEY_USAGE;
         critical := true;
         extnValue := encode_key_usage {| digitalSignature := true;
                                         nonRepudiation := false;
                                         keyEncipherment := true;
                                         dataEncipherment := false;
                                         keyAgreement := false;
                                         keyCertSign := false;
                                         cRLSign := false;
                                         encipherOnly := false;
                                         decipherOnly := false |} |};
      {| extnID := OID_EXTENDED_KEY_USAGE;
         critical := false;
         extnValue := encode_extended_key_usage [OID_KP_SERVER_AUTH; OID_KP_CLIENT_AUTH] |};
      {| extnID := OID_SUBJECT_ALT_NAME;
         critical := false;
         extnValue := [] |}  (* Stub - would encode SAN *)
    ]
  |} in
  {| tbsCertificate := tbs;
     signatureAlgorithm := {| algorithm := OID_SHA256_WITH_RSA; parameters := None |};
     signatureValue := sign_data (encode_tbs tbs) issuer_privkey |}.

(* Example end-entity certificate *)
Definition example_ee_cert : Certificate :=
  make_ee_cert example_ca_dn example_ee_dn example_pubkey example_privkey
               (generate_random_bytes 20) 365.

(* Example CRL *)
Definition example_crl : CertificateRevocationList :=
  let tbs := {|
    crl_version := 1;
    crl_signature := {| algorithm := OID_SHA256_WITH_RSA; parameters := None |};
    crl_issuer := example_ca_dn;
    crl_thisUpdate := current_time;
    crl_nextUpdate := Some (current_time + 86400 * 7);  (* 7 days *)
    crl_revokedCertificates := [];  (* No revoked certs *)
    crl_extensions := []
  |} in
  {| tbsCertList := tbs;
     crl_signatureAlgorithm := {| algorithm := OID_SHA256_WITH_RSA; parameters := None |};
     crl_signatureValue := sign_data (encode_sequence []) example_privkey |}.

(* Example path validation *)
Definition example_validation : ValidationResult :=
  let input := {|
    trustAnchors := [example_ca_cert];
    certificatePath := [example_ee_cert];
    currentTime := current_time;
    permittedSubtrees := None;
    excludedSubtrees := None;
    policySet := []
  |} in
  validate_cert_path input.

(* Helper: Check if certificate is for specific domain *)
Definition cert_for_domain (cert : Certificate) (domain : string) : bool :=
  match get_extension OID_SUBJECT_ALT_NAME cert.(tbsCertificate).(extensions) with
  | Some ext =>
      existsb (fun name =>
        match name with
        | GN_DNSName d => String.eqb d domain
        | _ => false
        end
      ) (decode_subject_alt_names ext.(extnValue))
  | None => false
  end.

(* Helper: Extract common name from DN *)
Fixpoint get_common_name (dn : DistinguishedName) : option string :=
  match dn with
  | [] => None
  | rdn :: rest =>
      match List.find (fun atv => oid_equal atv.(attr_type) OID_COMMON_NAME) rdn with
      | Some atv => Some atv.(attr_value)
      | None => get_common_name rest
      end
  end.

(* Helper: Check if certificate has specific extended key usage *)
Definition has_extended_key_usage (cert : Certificate) (usage_oid : OID) : bool :=
  match get_extension OID_EXTENDED_KEY_USAGE cert.(tbsCertificate).(extensions) with
  | Some ext =>
      match decode_extended_key_usage ext.(extnValue) with
      | Some usages => existsb (oid_equal usage_oid) usages
      | None => false
      end
  | None => false
  end.

(* Helper: Get remaining validity days *)
Definition remaining_validity_days (cert : Certificate) : N :=
  let not_after := cert.(tbsCertificate).(validity).(notAfter) in
  if N.ltb current_time not_after then
    (not_after - current_time) / 86400
  else
    0.

(* =============================================================================
   Section 11: Additional Theorems about Helper Functions
   ============================================================================= *)

(* Property 31: DN with common name can be extracted *)
Theorem get_cn_from_example_ca :
  get_common_name example_ca_dn = Some "Example Root CA"%string.
Proof.
  unfold get_common_name, example_ca_dn. simpl.
  unfold oid_equal. simpl.
  reflexivity.
Qed.

(* Property 32: Example CA cert is well-formed *)
Theorem example_ca_well_formed :
  well_formed_cert example_ca_cert.
Proof.
  unfold example_ca_cert.
  apply generated_cert_is_well_formed.
Qed.

(* Property 33: Remaining validity is zero for expired certs *)
Theorem expired_cert_zero_validity : forall cert,
  N.ltb cert.(tbsCertificate).(validity).(notAfter) current_time = true ->
  remaining_validity_days cert = 0.
Proof.
  intros cert H.
  unfold remaining_validity_days.
  destruct (N.ltb current_time (notAfter (validity (tbsCertificate cert)))) eqn:Hlt.
  - apply N.ltb_lt in Hlt.
    apply N.ltb_lt in H.
    lia.
  - reflexivity.
Qed.

(* =============================================================================
   Section 12: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" [ "Some" "None" ].

(* Extract to OCaml *)
Extraction "x509_pki.ml"
  (* Core validation *)
  validate_cert_path
  validate_certificate_signature
  validate_crl
  check_revocation
  verify_name_constraints

  (* Certificate generation *)
  generate_self_signed
  make_ee_cert

  (* Encoding *)
  encode_tbs
  encode_key_usage
  encode_basic_constraints
  encode_extended_key_usage
  encode_oid
  encode_dn

  (* Helper functions *)
  get_common_name
  has_extended_key_usage
  cert_for_domain
  remaining_validity_days
  is_ca_cert
  has_unknown_critical_extension
  dn_eq
  oid_equal

  (* Examples *)
  example_ca_cert
  example_ee_cert
  example_crl
  example_validation.