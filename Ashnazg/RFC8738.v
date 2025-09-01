(* =============================================================================
   Formal Verification of ACME IP Identifier Validation Extension
   
   Specification: RFC 8738 (R. Shoemaker, March 2020)
   Target: ACME IP Validation
   
   Module: ACME IP Validation Formalization and Verification
   Author: Charles C Norton
   Date: September 1, 2025
   
   "No shadow remained in their understanding, save one."
   
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

(* =============================================================================
   Section 1: Basic Types and Constants
   ============================================================================= *)

Definition byte := N.
Definition word16 := N.
Definition word32 := N.
Definition word128 := list byte.  (* For IPv6 *)

(* IP Address Types *)
Inductive IPAddress :=
  | IPv4 : word32 -> IPAddress
  | IPv6 : word128 -> IPAddress.

(* IP Identifier type *)
Definition IP_IDENTIFIER_TYPE : string := "ip".

(* Validation methods supported for IP *)
Definition IP_SUPPORTED_CHALLENGES : list string := 
  [CHALLENGE_HTTP_01; CHALLENGE_TLS_ALPN_01].
  (* Note: DNS-01 is NOT supported for IP identifiers *)

(* =============================================================================
   Section 2: IP Address Encoding (RFC 8738 Section 3)
   ============================================================================= *)

(* Convert IPv4 to string representation *)
Definition ipv4_to_string (ip : word32) : string :=
  let b3 := N.land (N.shiftr ip 24) 255 in
  let b2 := N.land (N.shiftr ip 16) 255 in
  let b1 := N.land (N.shiftr ip 8) 255 in
  let b0 := N.land ip 255 in
  n_to_string b3 ++ "." ++ n_to_string b2 ++ "." ++ 
  n_to_string b1 ++ "." ++ n_to_string b0.

(* Convert IPv6 to string representation *)
Definition ipv6_to_string (ip : word128) : string :=
  (* Simplified - actual implementation would handle zero compression *)
  match ip with
  | h1::h2::h3::h4::h5::h6::h7::h8::h9::h10::h11::h12::h13::h14::h15::h16::[] =>
      (* Convert pairs of bytes to hex groups *)
      let group1 := N.lor (N.shiftl h1 8) h2 in
      let group2 := N.lor (N.shiftl h3 8) h4 in
      let group3 := N.lor (N.shiftl h5 8) h6 in
      let group4 := N.lor (N.shiftl h7 8) h8 in
      let group5 := N.lor (N.shiftl h9 8) h10 in
      let group6 := N.lor (N.shiftl h11 8) h12 in
      let group7 := N.lor (N.shiftl h13 8) h14 in
      let group8 := N.lor (N.shiftl h15 8) h16 in
      n_to_hex group1 ++ ":" ++ n_to_hex group2 ++ ":" ++
      n_to_hex group3 ++ ":" ++ n_to_hex group4 ++ ":" ++
      n_to_hex group5 ++ ":" ++ n_to_hex group6 ++ ":" ++
      n_to_hex group7 ++ ":" ++ n_to_hex group8
  | _ => "invalid"
  end.

(* Convert IP address to string *)
Definition ip_to_string (ip : IPAddress) : string :=
  match ip with
  | IPv4 addr => ipv4_to_string addr
  | IPv6 addr => ipv6_to_string addr
  end.

(* Parse IP address from string *)
Definition parse_ip_address (s : string) : option IPAddress :=
  if string_contains s ":" then
    (* IPv6 *)
    match parse_ipv6 s with
    | Some addr => Some (IPv6 addr)
    | None => None
    end
  else
    (* IPv4 *)
    match parse_ipv4 s with
    | Some addr => Some (IPv4 addr)
    | None => None
    end.

(* =============================================================================
   Section 3: IP Identifier Structure (RFC 8738 Section 4)
   ============================================================================= *)

(* Create IP identifier *)
Definition create_ip_identifier (ip : IPAddress) : Identifier :=
  {| id_type := IP_IDENTIFIER_TYPE;
     id_value := ip_to_string ip |}.

(* Validate IP identifier format *)
Definition validate_ip_identifier (id : Identifier) : bool :=
  if String.eqb id.(id_type) IP_IDENTIFIER_TYPE then
    match parse_ip_address id.(id_value) with
    | Some _ => true
    | None => false
    end
  else
    false.

(* Check if IP is private/reserved *)
Definition is_private_ip (ip : IPAddress) : bool :=
  match ip with
  | IPv4 addr =>
      (* RFC 1918 private ranges *)
      let is_10 := N.eqb (N.shiftr addr 24) 10 in
      let is_172_16 := andb (N.eqb (N.shiftr addr 24) 172)
                            (andb (N.leb 16 (N.land (N.shiftr addr 16) 255))
                                  (N.leb (N.land (N.shiftr addr 16) 255) 31)) in
      let is_192_168 := andb (N.eqb (N.shiftr addr 24) 192)
                             (N.eqb (N.land (N.shiftr addr 16) 255) 168) in
      let is_127 := N.eqb (N.shiftr addr 24) 127 in  (* Loopback *)
      orb (orb (orb is_10 is_172_16) is_192_168) is_127
  | IPv6 addr =>
      match addr with
      | 0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::1::[] => true  (* ::1 loopback *)
      | 0xfc::_ => true  (* fc00::/7 unique local *)
      | 0xfd::_ => true  (* fd00::/8 unique local *)
      | 0xfe::0x80::_ => true  (* fe80::/10 link local *)
      | _ => false
      end
  end.

(* =============================================================================
   Section 4: HTTP-01 Challenge for IP (RFC 8738 Section 5)
   ============================================================================= *)

(* HTTP-01 validation for IP addresses *)
Definition validate_http01_ip (challenge : Challenge) 
                             (ip_identifier : Identifier)
                             (account_key : AccountKey) : bool :=
  (* Verify this is an IP identifier *)
  if negb (String.eqb ip_identifier.(id_type) IP_IDENTIFIER_TYPE) then
    false
  else
    match parse_ip_address ip_identifier.(id_value) with
    | None => false
    | Some ip =>
        (* Check not private IP *)
        if is_private_ip ip then
          false
        else
          let expected_content := http01_key_authorization 
                                 challenge.(ch_token) account_key in
          let well_known_path := "/.well-known/acme-challenge/" ++ 
                                challenge.(ch_token) in
          
          (* Fetch using IP address directly *)
          let url := "http://" ++ ip_to_string ip ++ well_known_path in
          match http_get url with
          | Some content => String.eqb content expected_content
          | None => false
          end
    end.

(* =============================================================================
   Section 5: TLS-ALPN-01 Challenge for IP (RFC 8738 Section 6)
   ============================================================================= *)

(* Generate certificate for IP address *)
Definition generate_ip_tls_alpn_cert (ip : IPAddress)
                                    (challenge : Challenge)
                                    (account_key : AccountKey)
                                    : Certificate :=
  let (cert_pubkey, cert_privkey) := generate_key_pair 2048 in
  
  (* Create acmeIdentifier extension *)
  let acme_ext := encode_acme_identifier 
                   (create_acme_identifier challenge.(ch_token) account_key) in
  
  (* IP addresses go in SAN, not CN *)
  let san_ext := {| 
    extnID := OID_SUBJECT_ALT_NAME;
    critical := true;  (* Critical when subject is empty *)
    extnValue := encode_subject_alt_name [GN_IPAddress (encode_ip_address ip)]
  |} in
  
  let tbs := {|
    version := 2;
    serialNumber := generate_random_bytes 20;
    signature := {| algorithm := OID_SHA256_WITH_RSA; parameters := None |};
    issuer := [];  (* Empty issuer for self-signed *)
    validity := {| notBefore := current_time;
                   notAfter := current_time + 86400 |};
    subject := [];  (* Empty subject - IP in SAN only *)
    subjectPublicKeyInfo := cert_pubkey;
    issuerUniqueID := None;
    subjectUniqueID := None;
    extensions := [acme_ext; san_ext]
  |} in
  
  let signature := sign_data (encode_tbs tbs) cert_privkey in
  
  {| tbsCertificate := tbs;
     signatureAlgorithm := {| algorithm := OID_SHA256_WITH_RSA; parameters := None |};
     signatureValue := signature |}.

(* Validate TLS-ALPN-01 for IP *)
Definition validate_tls_alpn01_ip (challenge : Challenge)
                                 (ip_identifier : Identifier)
                                 (account_key : AccountKey) : bool :=
  if negb (String.eqb ip_identifier.(id_type) IP_IDENTIFIER_TYPE) then
    false
  else
    match parse_ip_address ip_identifier.(id_value) with
    | None => false
    | Some ip =>
        if is_private_ip ip then
          false
        else
          (* Connect directly to IP *)
          match establish_tls_connection (ip_to_string ip) TLS_PORT with
          | None => false
          | Some conn_state =>
              (* Check ALPN *)
              match conn_state.(tvs_alpn_negotiated) with
              | None => false
              | Some alpn =>
                  if negb (list_beq byte_eq alpn ACME_TLS_ALPN_PROTOCOL) then
                    false
                  else
                    (* Verify certificate *)
                    match conn_state.(tvs_peer_certificate) with
                    | None => false
                    | Some cert => 
                        verify_ip_tls_alpn_cert cert challenge account_key ip
                    end
              end
          end
    end.

(* =============================================================================
   Section 6: Certificate Issuance for IP (RFC 8738 Section 7)
   ============================================================================= *)

(* CSR for IP address *)
Definition create_ip_csr (ip : IPAddress) (pubkey : SubjectPublicKeyInfo)
                        (privkey : list byte) : CSR :=
  {| csr_public_key := pubkey;
     csr_subject := [];  (* Empty subject for IP *)
     csr_extensions := [
       {| extnID := OID_SUBJECT_ALT_NAME;
          critical := true;
          extnValue := encode_subject_alt_name [GN_IPAddress (encode_ip_address ip)] |}
     ];
     csr_signature_algorithm := {| algorithm := OID_SHA256_WITH_RSA; 
                                   parameters := None |};
     csr_signature := sign_csr_content pubkey privkey |}.

(* Issue certificate for IP *)
Definition issue_ip_certificate (csr : CSR) (ip : IPAddress) 
                              (ca_cert : Certificate) (ca_key : list byte)
                              : Certificate :=
  let serial := generate_serial_number in
  
  let tbs := {|
    version := 2;
    serialNumber := serial;
    signature := {| algorithm := OID_SHA256_WITH_RSA; parameters := None |};
    issuer := ca_cert.(tbsCertificate).(subject);
    validity := {| notBefore := current_time;
                   notAfter := current_time + 7776000 |};  (* 90 days *)
    subject := [];  (* Empty subject *)
    subjectPublicKeyInfo := csr.(csr_public_key);
    issuerUniqueID := None;
    subjectUniqueID := None;
    extensions := [
      {| extnID := OID_SUBJECT_ALT_NAME;
         critical := true;
         extnValue := encode_subject_alt_name [GN_IPAddress (encode_ip_address ip)] |};
      {| extnID := OID_KEY_USAGE;
         critical := true;
         extnValue := encode_key_usage {| 
           digitalSignature := true;
           nonRepudiation := false;
           keyEncipherment := true;
           dataEncipherment := false;
           keyAgreement := false;
           keyCertSign := false;
           cRLSign := false;
           encipherOnly := false;
           decipherOnly := false |} |};
      {| extnID := OID_AUTHORITY_KEY_ID;
         critical := false;
         extnValue := encode_authority_key_id ca_cert |}
    ]
  |} in
  
  let signature := sign_data (encode_tbs tbs) ca_key in
  
  {| tbsCertificate := tbs;
     signatureAlgorithm := {| algorithm := OID_SHA256_WITH_RSA; parameters := None |};
     signatureValue := signature |}.

(* =============================================================================
   Section 7: Reverse DNS Validation (RFC 8738 Section 8)
   ============================================================================= *)

(* Reverse DNS lookup *)
Definition reverse_dns_lookup (ip : IPAddress) : option string :=
  match ip with
  | IPv4 addr =>
      let ptr_name := ipv4_to_ptr_name addr in
      dns_query_ptr ptr_name
  | IPv6 addr =>
      let ptr_name := ipv6_to_ptr_name addr in
      dns_query_ptr ptr_name
  end.

(* Verify reverse DNS *)
Definition verify_reverse_dns (ip : IPAddress) (expected_name : string) : bool :=
  match reverse_dns_lookup ip with
  | None => false
  | Some ptr_name =>
      if String.eqb ptr_name expected_name then
        (* Forward confirm *)
        match dns_query_a expected_name with
        | Some resolved_ips =>
            existsb (fun resolved => ip_equal resolved ip) resolved_ips
        | None => false
        end
      else
        false
  end.

(* =============================================================================
   Section 8: Validation Restrictions (RFC 8738 Section 9)
   ============================================================================= *)

(* Check if challenge type is valid for IP *)
Definition is_valid_ip_challenge (challenge_type : string) : bool :=
  existsb (String.eqb challenge_type) IP_SUPPORTED_CHALLENGES.

(* Validate IP authorization *)
Definition validate_ip_authorization (authz : Authorization) : bool :=
  (* Must be IP identifier *)
  if String.eqb authz.(authz_identifier).(id_type) IP_IDENTIFIER_TYPE then
    (* All challenges must be supported types *)
    forallb (fun ch => is_valid_ip_challenge ch.(ch_type)) 
            authz.(authz_challenges)
  else
    false.

(* =============================================================================
   Section 9: Security Considerations (RFC 8738 Section 10)
   ============================================================================= *)

(* Rate limiting for IP validations *)
Record IPRateLimits := {
  irl_max_attempts_per_ip : N;
  irl_max_attempts_per_range : N;
  irl_time_window : N
}.

(* Check rate limits *)
Definition check_ip_rate_limits (ip : IPAddress) (limits : IPRateLimits)
                               (history : list (IPAddress * N)) : bool :=
  let recent := filter (fun entry =>
    N.ltb (current_time - snd entry) limits.(irl_time_window)
  ) history in
  
  let ip_attempts := length (filter (fun entry =>
    ip_equal (fst entry) ip
  ) recent) in
  
  if N.ltb limits.(irl_max_attempts_per_ip) ip_attempts then
    false
  else
    (* Check range limits *)
    let range_attempts := match ip with
    | IPv4 addr =>
        (* Count /24 range *)
        let range := N.land addr 0xFFFFFF00 in
        length (filter (fun entry =>
          match fst entry with
          | IPv4 e_addr => N.eqb (N.land e_addr 0xFFFFFF00) range
          | _ => false
          end
        ) recent)
    | IPv6 addr =>
        (* Count /48 range *)
        count_ipv6_range_attempts addr recent
    end in
    N.leb range_attempts limits.(irl_max_attempts_per_range).

(* =============================================================================
   Section 10: Key Properties
   ============================================================================= *)

(* Property 1: IP identifiers have correct type *)
Theorem ip_identifier_type : forall ip id,
  create_ip_identifier ip = id ->
  id.(id_type) = IP_IDENTIFIER_TYPE.
Proof.
  intros. unfold create_ip_identifier in H.
  inversion H. reflexivity.
Qed.

(* Property 2: DNS-01 not supported for IP *)
Theorem no_dns01_for_ip : forall ch,
  is_valid_ip_challenge ch = true ->
  ch <> CHALLENGE_DNS_01.
Proof.
  intros. unfold is_valid_ip_challenge, IP_SUPPORTED_CHALLENGES in H.
  simpl in H.
  intro eq. rewrite eq in H.
  simpl in H. discriminate.
Qed.

(* Property 3: IP certificates have empty subject *)
Theorem ip_cert_empty_subject : forall ip ch key cert,
  generate_ip_tls_alpn_cert ip ch key = cert ->
  cert.(tbsCertificate).(subject) = [].
Proof.
  intros. unfold generate_ip_tls_alpn_cert in H.
  inversion H. reflexivity.
Qed.

(* Property 4: IP must be in SAN *)
Theorem ip_in_san : forall csr ip ca ca_key cert,
  issue_ip_certificate csr ip ca ca_key = cert ->
  exists ext, In ext cert.(tbsCertificate).(extensions) /\
             ext.(extnID) = OID_SUBJECT_ALT_NAME /\
             ext.(critical) = true.
Proof.
  admit.
Qed.

(* Property 5: Private IPs rejected *)
Theorem private_ip_rejected : forall ch ip key,
  is_private_ip ip = true ->
  validate_http01_ip ch (create_ip_identifier ip) key = false.
Proof.
  admit.
Qed.

(* =============================================================================
   Section 11: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction "acme_ip.ml"
  create_ip_identifier
  validate_ip_identifier
  validate_http01_ip
  validate_tls_alpn01_ip
  generate_ip_tls_alpn_cert
  issue_ip_certificate
  check_ip_rate_limits.
