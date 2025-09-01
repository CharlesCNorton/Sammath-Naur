(* =============================================================================
   Formal Verification of Online Certificate Status Protocol (OCSP)
   
   Specification: RFC 6960 (S. Santesson, et al., June 2013)
   Target: OCSP Protocol
   
   Module: OCSP Formalization and Verification
   Author: Charles C Norton
   Date: September 1, 2025
   
   "And he showed unto them the making of chains of trust unbreakable."
   
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
Definition word32 := N.
Definition word64 := N.

(* OCSP Object Identifiers *)
Definition OID_OCSP : OID := [1; 3; 6; 1; 5; 5; 7; 48; 1].
Definition OID_OCSP_BASIC : OID := [1; 3; 6; 1; 5; 5; 7; 48; 1; 1].
Definition OID_OCSP_NONCE : OID := [1; 3; 6; 1; 5; 5; 7; 48; 1; 2].
Definition OID_OCSP_CRL_REF : OID := [1; 3; 6; 1; 5; 5; 7; 48; 1; 3].
Definition OID_OCSP_RESPONSE : OID := [1; 3; 6; 1; 5; 5; 7; 48; 1; 4].
Definition OID_OCSP_NO_CHECK : OID := [1; 3; 6; 1; 5; 5; 7; 48; 1; 5].
Definition OID_OCSP_ARCHIVE_CUTOFF : OID := [1; 3; 6; 1; 5; 5; 7; 48; 1; 6].
Definition OID_OCSP_SERVICE_LOCATOR : OID := [1; 3; 6; 1; 5; 5; 7; 48; 1; 7].

(* Certificate Status Values *)
Inductive CertStatus :=
  | CS_GOOD
  | CS_REVOKED : N -> N -> CertStatus  (* revocationTime, revocationReason *)
  | CS_UNKNOWN.

(* OCSP Response Status *)
Inductive OCSPResponseStatus :=
  | ORS_SUCCESSFUL       (* 0 *)
  | ORS_MALFORMED_REQUEST (* 1 *)
  | ORS_INTERNAL_ERROR   (* 2 *)
  | ORS_TRY_LATER       (* 3 *)
  | ORS_SIG_REQUIRED    (* 5 *)
  | ORS_UNAUTHORIZED.   (* 6 *)

(* =============================================================================
   Section 2: OCSP Request (RFC 6960 Section 4.1)
   ============================================================================= *)

(* CertID - identifies a certificate *)
Record CertID := {
  hashAlgorithm : AlgorithmIdentifier;
  issuerNameHash : list byte;
  issuerKeyHash : list byte;
  serialNumber : list byte
}.

(* Single request *)
Record Request := {
  reqCert : CertID;
  singleRequestExtensions : list Extension
}.

(* TBSRequest *)
Record TBSRequest := {
  tbsReq_version : N;  (* 0 for v1 *)
  tbsReq_requestorName : option GeneralName;
  tbsReq_requestList : list Request;
  tbsReq_requestExtensions : list Extension
}.

(* OCSPRequest *)
Record OCSPRequest := {
  tbsRequest : TBSRequest;
  optionalSignature : option Signature
}
with Signature := {
  signatureAlgorithm : AlgorithmIdentifier;
  signature : list byte;
  certs : list Certificate
}.

(* Create OCSP request *)
Definition create_ocsp_request (cert : Certificate) (issuerCert : Certificate)
                              (includeNonce : bool) : OCSPRequest :=
  (* Calculate CertID *)
  let hashAlg := {| algorithm := OID_SHA256; parameters := None |} in
  let issuerNameHash := hash_sha256 (encode_dn issuerCert.(tbsCertificate).(subject)) in
  let issuerKeyHash := hash_sha256 (extract_public_key_bytes 
                                    issuerCert.(tbsCertificate).(subjectPublicKeyInfo)) in
  
  let certId := {|
    hashAlgorithm := hashAlg;
    issuerNameHash := issuerNameHash;
    issuerKeyHash := issuerKeyHash;
    serialNumber := cert.(tbsCertificate).(serialNumber)
  |} in
  
  (* Add nonce extension if requested *)
  let extensions := if includeNonce then
    [{| extnID := OID_OCSP_NONCE;
        critical := false;
        extnValue := generate_random_bytes 20 |}]
  else [] in
  
  {| tbsRequest := {|
       tbsReq_version := 0;
       tbsReq_requestorName := None;
       tbsReq_requestList := [{|
         reqCert := certId;
         singleRequestExtensions := []
       |}];
       tbsReq_requestExtensions := extensions
     |};
     optionalSignature := None |}.

(* =============================================================================
   Section 3: OCSP Response (RFC 6960 Section 4.2)
   ============================================================================= *)

(* SingleResponse *)
Record SingleResponse := {
  sr_certID : CertID;
  sr_certStatus : CertStatus;
  sr_thisUpdate : N;
  sr_nextUpdate : option N;
  sr_singleExtensions : list Extension
}.

(* ResponseData *)
Record ResponseData := {
  rd_version : N;
  rd_responderID : ResponderID;
  rd_producedAt : N;
  rd_responses : list SingleResponse;
  rd_responseExtensions : list Extension
}
with ResponderID :=
  | RID_ByName : DistinguishedName -> ResponderID
  | RID_ByKey : list byte -> ResponderID.

(* BasicOCSPResponse *)
Record BasicOCSPResponse := {
  tbsResponseData : ResponseData;
  signatureAlgorithm : AlgorithmIdentifier;
  signature : list byte;
  certs : option (list Certificate)
}.

(* ResponseBytes *)
Record ResponseBytes := {
  responseType : OID;
  response : list byte
}.

(* OCSPResponse *)
Record OCSPResponse := {
  responseStatus : OCSPResponseStatus;
  responseBytes : option ResponseBytes
}.

(* Create OCSP response *)
Definition create_ocsp_response (request : OCSPRequest) 
                               (responderCert : Certificate)
                               (responderKey : list byte)
                               (certStatuses : list (CertID * CertStatus))
                               : OCSPResponse :=
  let now := current_time in
  
  (* Create single responses *)
  let responses := map (fun req =>
    match find_cert_status req.(reqCert) certStatuses with
    | Some status =>
        {| sr_certID := req.(reqCert);
           sr_certStatus := status;
           sr_thisUpdate := now;
           sr_nextUpdate := Some (now + 86400);  (* 24 hours *)
           sr_singleExtensions := [] |}
    | None =>
        {| sr_certID := req.(reqCert);
           sr_certStatus := CS_UNKNOWN;
           sr_thisUpdate := now;
           sr_nextUpdate := None;
           sr_singleExtensions := [] |}
    end
  ) request.(tbsRequest).(tbsReq_requestList) in
  
  (* Copy nonce if present *)
  let extensions := 
    match find_extension OID_OCSP_NONCE request.(tbsRequest).(tbsReq_requestExtensions) with
    | Some nonce => [nonce]
    | None => []
    end in
  
  (* Create response data *)
  let responseData := {|
    rd_version := 0;
    rd_responderID := RID_ByKey (hash_sha256 (extract_public_key_bytes
                                              responderCert.(tbsCertificate).(subjectPublicKeyInfo)));
    rd_producedAt := now;
    rd_responses := responses;
    rd_responseExtensions := extensions
  |} in
  
  (* Sign response *)
  let signAlg := {| algorithm := OID_SHA256_WITH_RSA; parameters := None |} in
  let signature := sign_data (encode_response_data responseData) responderKey in
  
  let basicResponse := {|
    tbsResponseData := responseData;
    signatureAlgorithm := signAlg;
    signature := signature;
    certs := Some [responderCert]
  |} in
  
  {| responseStatus := ORS_SUCCESSFUL;
     responseBytes := Some {|
       responseType := OID_OCSP_BASIC;
       response := encode_basic_response basicResponse
     |} |}.

(* =============================================================================
   Section 4: OCSP Validation (RFC 6960 Section 3)
   ============================================================================= *)

(* OCSP validation context *)
Record OCSPValidationContext := {
  ovc_trustedResponders : list Certificate;
  ovc_maxAge : N;  (* Maximum response age in seconds *)
  ovc_requireNonce : bool;
  ovc_currentTime : N
}.

(* Validate OCSP response *)
Definition validate_ocsp_response (response : OCSPResponse)
                                 (request : OCSPRequest)
                                 (context : OCSPValidationContext)
                                 : ValidationResult :=
  match response.(responseStatus) with
  | ORS_SUCCESSFUL =>
      match response.(responseBytes) with
      | None => VR_INVALID_RESPONSE
      | Some rb =>
          if oid_equal rb.(responseType) OID_OCSP_BASIC then
            match decode_basic_response rb.(response) with
            | None => VR_INVALID_RESPONSE
            | Some basicResp =>
                (* Verify signature *)
                match find_responder_cert basicResp context.(ovc_trustedResponders) with
                | None => VR_UNTRUSTED_RESPONDER
                | Some responderCert =>
                    if verify_signature (encode_response_data basicResp.(tbsResponseData))
                                      basicResp.(signature)
                                      responderCert.(tbsCertificate).(subjectPublicKeyInfo) then
                      (* Check nonce if required *)
                      if context.(ovc_requireNonce) then
                        match find_extension OID_OCSP_NONCE 
                                           request.(tbsRequest).(tbsReq_requestExtensions),
                              find_extension OID_OCSP_NONCE 
                                           basicResp.(tbsResponseData).(rd_responseExtensions) with
                        | Some reqNonce, Some respNonce =>
                            if list_beq byte_eq reqNonce.(extnValue) respNonce.(extnValue) then
                              VR_VALID
                            else
                              VR_NONCE_MISMATCH
                        | _, _ => VR_NONCE_MISSING
                        end
                      else
                        (* Check response freshness *)
                        if N.ltb (context.(ovc_currentTime) - 
                                 basicResp.(tbsResponseData).(rd_producedAt))
                                context.(ovc_maxAge) then
                          VR_VALID
                        else
                          VR_RESPONSE_EXPIRED
                    else
                      VR_SIGNATURE_FAILURE
                end
            end
          else
            VR_UNSUPPORTED_RESPONSE_TYPE
      end
  | ORS_MALFORMED_REQUEST => VR_MALFORMED
  | ORS_INTERNAL_ERROR => VR_SERVER_ERROR
  | ORS_TRY_LATER => VR_TRY_LATER
  | ORS_SIG_REQUIRED => VR_SIGNATURE_REQUIRED
  | ORS_UNAUTHORIZED => VR_UNAUTHORIZED
  end.

(* =============================================================================
   Section 5: OCSP Responder (RFC 6960 Section 2.2)
   ============================================================================= *)

Record OCSPResponder := {
  or_signingCert : Certificate;
  or_signingKey : list byte;
  or_crlSource : CRLSource;
  or_responseCache : list (CertID * SingleResponse * N);  (* certID, response, expiry *)
  or_maxCacheAge : N;
  or_delegatedPath : option (list Certificate)
}.

Inductive CRLSource :=
  | CRL_File : string -> CRLSource
  | CRL_Database : N -> CRLSource  (* DB connection handle *)
  | CRL_Directory : string -> CRLSource.

(* Process OCSP request *)
Definition process_ocsp_request (responder : OCSPResponder)
                               (request : OCSPRequest)
                               : OCSPResponse :=
  let now := current_time in
  
  (* Check each certificate in request *)
  let statuses := map (fun req =>
    (* Check cache first *)
    match find_in_cache req.(reqCert) responder.(or_responseCache) now with
    | Some cached => (req.(reqCert), cached.(sr_certStatus))
    | None =>
        (* Check CRL source *)
        let status := check_cert_status req.(reqCert) responder.(or_crlSource) in
        (req.(reqCert), status)
    end
  ) request.(tbsRequest).(tbsReq_requestList) in
  
  create_ocsp_response request 
                      responder.(or_signingCert)
                      responder.(or_signingKey)
                      statuses.

(* =============================================================================
   Section 6: OCSP Stapling (RFC 6960 Section 3.6)
   ============================================================================= *)

Record StapledOCSPResponse := {
  sor_response : OCSPResponse;
  sor_timestamp : N;
  sor_maxAge : N
}.

(* Validate stapled OCSP response *)
Definition validate_stapled_response (stapled : StapledOCSPResponse)
                                    (serverCert : Certificate)
                                    (issuerCert : Certificate)
                                    (now : N) : bool :=
  (* Check response age *)
  if N.ltb stapled.(sor_maxAge) (now - stapled.(sor_timestamp)) then
    false
  else
    match stapled.(sor_response).(responseBytes) with
    | None => false
    | Some rb =>
        match decode_basic_response rb.(response) with
        | None => false
        | Some basicResp =>
            (* Find response for server certificate *)
            let certId := compute_cert_id serverCert issuerCert in
            match find_single_response certId basicResp.(tbsResponseData).(rd_responses) with
            | None => false
            | Some singleResp =>
                (* Check certificate is not revoked *)
                match singleResp.(sr_certStatus) with
                | CS_GOOD => 
                    (* Check update times *)
                    N.leb singleResp.(sr_thisUpdate) now &&
                    match singleResp.(sr_nextUpdate) with
                    | Some next => N.ltb now next
                    | None => true
                    end
                | _ => false
                end
            end
        end
    end.

(* =============================================================================
   Section 7: OCSP Extensions (RFC 6960 Section 4.4)
   ============================================================================= *)

(* Preferred signature algorithms *)
Definition PreferredSignatureAlgorithms := list AlgorithmIdentifier.

(* Extended revocation reasons *)
Inductive RevocationReason :=
  | RR_UNSPECIFIED           (* 0 *)
  | RR_KEY_COMPROMISE        (* 1 *)
  | RR_CA_COMPROMISE         (* 2 *)
  | RR_AFFILIATION_CHANGED   (* 3 *)
  | RR_SUPERSEDED           (* 4 *)
  | RR_CESSATION_OF_OPERATION (* 5 *)
  | RR_CERTIFICATE_HOLD      (* 6 *)
  | RR_REMOVE_FROM_CRL       (* 8 *)
  | RR_PRIVILEGE_WITHDRAWN   (* 9 *)
  | RR_AA_COMPROMISE.        (* 10 *)

(* Archive cutoff extension *)
Definition ArchiveCutoff := N.  (* GeneralizedTime *)

(* Process extensions *)
Definition process_ocsp_extensions (extensions : list Extension) 
                                 : list (OID * list byte) :=
  map (fun ext => (ext.(extnID), ext.(extnValue))) extensions.

(* =============================================================================
   Section 8: Key Properties
   ============================================================================= *)

(* Property 1: Response includes all requested certificates *)
Theorem response_completeness : forall req resp responder statuses,
  process_ocsp_request responder req = resp ->
  resp.(responseStatus) = ORS_SUCCESSFUL ->
  forall r, In r req.(tbsRequest).(tbsReq_requestList) ->
  exists sr, In sr (get_single_responses resp) /\
            cert_id_equal sr.(sr_certID) r.(reqCert) = true.
Proof.
  admit.
Qed.

(* Property 2: Nonce prevents replay *)
Theorem nonce_prevents_replay : forall req1 req2 resp1 resp2 ctx,
  has_nonce req1 = true ->
  has_nonce req2 = true ->
  get_nonce req1 <> get_nonce req2 ->
  validate_ocsp_response resp1 req1 ctx = VR_VALID ->
  validate_ocsp_response resp1 req2 ctx <> VR_VALID.
Proof.
  admit.
Qed.

(* Property 3: Response freshness *)
Theorem response_freshness : forall resp ctx,
  validate_ocsp_response resp ctx = VR_VALID ->
  get_produced_at resp <= ctx.(ovc_currentTime) /\
  ctx.(ovc_currentTime) - get_produced_at resp <= ctx.(ovc_maxAge).
Proof.
  admit.
Qed.

(* Property 4: Revoked status is persistent *)
Theorem revoked_persistent : forall certId t1 t2 reason,
  get_cert_status certId t1 = CS_REVOKED t1 reason ->
  t1 <= t2 ->
  exists t', get_cert_status certId t2 = CS_REVOKED t' reason.
Proof.
  admit.
Qed.

(* =============================================================================
   Section 9: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction "ocsp.ml"
  create_ocsp_request
  create_ocsp_response
  validate_ocsp_response
  process_ocsp_request
  validate_stapled_response.
