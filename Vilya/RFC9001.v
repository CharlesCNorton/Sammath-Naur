(* =============================================================================
   Formal Verification of Using TLS to Secure QUIC
   RFC 9001 (M. Thomson, S. Turner, May 2021)
   Author: Charles C Norton
   Date: September 1, 2025
   ============================================================================= *)

From Coq Require Import
  List
  NArith.NArith
  Bool
  Arith
  Lia
  String
  Ascii.

Import ListNotations.
Import List.
Open Scope N_scope.

(* =============================================================================
   Section 1: Basic Types and Constants
   ============================================================================= *)

Definition byte := N.
Definition word16 := N.
Definition word32 := N.
Definition word64 := N.

Definition AEAD_TAG_LENGTH : N := 16.
Definition SAMPLE_LENGTH : N := 16.
Definition MAX_AEAD_EXPANSION : N := 16.
Definition QUIC_VERSION_1 : word32 := 0x00000001.

Definition TLS_VERSION_13 : word16 := 0x0304.
Definition TLS_HANDSHAKE_CLIENTHELLO : byte := 1.
Definition TLS_HANDSHAKE_SERVERHELLO : byte := 2.
Definition TLS_HANDSHAKE_ENCRYPTED_EXTENSIONS : byte := 8.
Definition TLS_HANDSHAKE_CERTIFICATE : byte := 11.
Definition TLS_HANDSHAKE_CERTIFICATE_VERIFY : byte := 15.
Definition TLS_HANDSHAKE_FINISHED : byte := 20.

(* =============================================================================
   Section 2: Cryptographic Primitives
   ============================================================================= *)

(* XOR operation on bytes *)
Definition xor_byte (a b : byte) : byte := N.lxor a b.

(* XOR operation on byte lists *)
Fixpoint xor_bytes (a b : list byte) : list byte :=
  match a, b with
  | [], _ => []
  | _, [] => []
  | x::xs, y::ys => (xor_byte x y) :: xor_bytes xs ys
  end.

(* Lemma: XOR is self-inverse for bytes *)
Lemma xor_byte_involutive : forall a b,
  xor_byte (xor_byte a b) b = a.
Proof.
  intros. unfold xor_byte.
  rewrite N.lxor_assoc.
  rewrite N.lxor_nilpotent.
  rewrite N.lxor_0_r.
  reflexivity.
Qed.

(* Lemma: XOR is self-inverse for byte lists *)
Lemma xor_bytes_involutive : forall a b,
  length a = length b ->
  xor_bytes (xor_bytes a b) b = a.
Proof.
  induction a; intros.
  - simpl. reflexivity.
  - destruct b.
    + simpl in H. discriminate.
    + simpl. f_equal.
      * apply xor_byte_involutive.
      * apply IHa. simpl in H. injection H. auto.
Qed.

(* Lemma: xor_bytes preserves length when inputs have same length *)
Lemma xor_bytes_length : forall a b,
  length a = length b ->
  length (xor_bytes a b) = length a.
Proof.
  induction a; intros.
  - simpl. reflexivity.
  - destruct b.
    + simpl in H. discriminate.
    + simpl. f_equal. apply IHa.
      simpl in H. injection H. auto.
Qed.

(* Simple hash function (sum mod 256) *)
Definition simple_hash (data : list byte) : list byte :=
  let sum := fold_left N.add data 0 in
  repeat (N.modulo sum 256) 32.

(* HMAC simplified - XOR with padded key then hash *)
Definition hmac (key : list byte) (message : list byte) : list byte :=
  let padded_key := firstn 32 (key ++ repeat 0 32) in
  let ipad := repeat 0x36 32 in
  let opad := repeat 0x5C 32 in
  let inner := simple_hash (xor_bytes padded_key ipad ++ message) in
  simple_hash (xor_bytes padded_key opad ++ inner).

(* HKDF-Extract *)
Definition hkdf_extract (salt : list byte) (ikm : list byte) : list byte :=
  hmac salt ikm.

(* HKDF-Expand *)
Fixpoint hkdf_expand_core (prk : list byte) (info : list byte) 
                          (length : nat) (counter : byte) (acc : list byte) : list byte :=
  match length with
  | O => acc
  | S n' =>
      let block := hmac prk (acc ++ info ++ [counter]) in
      hkdf_expand_core prk info n' (N.succ counter) (acc ++ block)
  end.

Definition hkdf_expand (prk : list byte) (info : list byte) (length : N) : list byte :=
  firstn (N.to_nat length) (hkdf_expand_core prk info (N.to_nat (length / 32) + 1) 1 []).

(* Convert ASCII string to bytes *)
Definition string_to_bytes (s : string) : list byte :=
  map (fun c => N.of_nat (nat_of_ascii c)) (list_ascii_of_string s).

(* HKDF-Expand-Label for QUIC *)
Definition hkdf_expand_label (secret : list byte) (label : string) (length : N) : list byte :=
  let quic_label := string_to_bytes ("tls13 " ++ label) in
  let info := [N.shiftr length 8; N.land length 0xFF] ++ 
              [N.of_nat (List.length quic_label)] ++ quic_label ++ [0] in
  hkdf_expand secret info length.

(* =============================================================================
   Section 3: Initial Secrets (RFC 9001 Section 5.2)
   ============================================================================= *)

Definition INITIAL_SALT_V1 : list byte :=
  [0x38; 0x76; 0x2c; 0xf7; 0xf5; 0x59; 0x34; 0xb3;
   0x4d; 0x17; 0x9a; 0xe6; 0xa4; 0xc8; 0x0c; 0xad;
   0xcc; 0xbb; 0x7f; 0x0a].

Definition derive_initial_secrets (dcid : list byte) : (list byte * list byte) :=
  let initial_secret := hkdf_extract INITIAL_SALT_V1 dcid in
  let client_initial := hkdf_expand_label initial_secret "client in" 32 in
  let server_initial := hkdf_expand_label initial_secret "server in" 32 in
  (client_initial, server_initial).

(* =============================================================================
   Section 4: AEAD Functions (RFC 9001 Section 5.3)
   ============================================================================= *)

Record AEADContext := {
  aead_key : list byte;
  aead_iv : list byte;
  aead_hp_key : list byte
}.

(* Construct nonce from IV and packet number *)
Definition construct_nonce (iv : list byte) (pn : word64) : list byte :=
  let pn_bytes := [N.shiftr pn 56; N.shiftr pn 48; N.shiftr pn 40; N.shiftr pn 32;
                   N.shiftr pn 24; N.shiftr pn 16; N.shiftr pn 8; N.land pn 0xFF] in
  let padded_pn := repeat 0 4 ++ pn_bytes in
  xor_bytes iv padded_pn.

(* Simplified GCM-like AEAD *)
Definition aead_encrypt (ctx : AEADContext) (plaintext : list byte) 
                        (aad : list byte) (packet_number : word64) : list byte :=
  let nonce := construct_nonce ctx.(aead_iv) packet_number in
  let keystream := simple_hash (ctx.(aead_key) ++ nonce ++ aad) in
  let ciphertext := xor_bytes plaintext (firstn (length plaintext) keystream) in
  let tag := firstn (N.to_nat AEAD_TAG_LENGTH) 
                    (simple_hash (ctx.(aead_key) ++ nonce ++ aad ++ ciphertext)) in
  ciphertext ++ tag.

Definition aead_decrypt (ctx : AEADContext) (ciphertext_with_tag : list byte)
                        (aad : list byte) (packet_number : word64) : option (list byte) :=
  let ciphertext_len := length ciphertext_with_tag in
  if Nat.leb ciphertext_len (N.to_nat AEAD_TAG_LENGTH) then
    None
  else
    let ciphertext := firstn (ciphertext_len - N.to_nat AEAD_TAG_LENGTH) ciphertext_with_tag in
    let tag := skipn (ciphertext_len - N.to_nat AEAD_TAG_LENGTH) ciphertext_with_tag in
    let nonce := construct_nonce ctx.(aead_iv) packet_number in
    let expected_tag := firstn (N.to_nat AEAD_TAG_LENGTH)
                               (simple_hash (ctx.(aead_key) ++ nonce ++ aad ++ ciphertext)) in
    if list_eq_dec N.eq_dec tag expected_tag then
      let keystream := simple_hash (ctx.(aead_key) ++ nonce ++ aad) in
      Some (xor_bytes ciphertext (firstn (length ciphertext) keystream))
    else
      None.

(* Header protection using AES-ECB mode simulation *)
Definition header_protection_mask (hp_key : list byte) (sample : list byte) : list byte :=
  firstn 5 (simple_hash (hp_key ++ sample)).

Definition apply_header_protection (hp_key : list byte) (sample : list byte)
                                  (header : list byte) : list byte :=
  let mask := header_protection_mask hp_key sample in
  match header with
  | [] => []
  | h::rest => 
      let pn_length := 4%nat in (* Use nat literal *)
      let protected_first := xor_byte h (nth 0 mask 0) in
      let protected_pn := xor_bytes (firstn pn_length rest) (skipn 1 mask) in
      let unprotected_rest := skipn pn_length rest in
      protected_first :: protected_pn ++ unprotected_rest
  end.

Definition remove_header_protection (hp_key : list byte) (sample : list byte)
                                   (header : list byte) : list byte :=
  apply_header_protection hp_key sample header. (* XOR is self-inverse *)

(* =============================================================================
   Section 5: Packet Protection (RFC 9001 Section 5.4)
   ============================================================================= *)

Record ProtectedPacket := {
  pp_header : list byte;
  pp_encrypted_pn : list byte;
  pp_payload : list byte
}.

Inductive EncryptionLevel :=
  | EncInitial
  | EncEarlyData
  | EncHandshake
  | EncApplication.

Record KeyMaterial := {
  km_write_key : list byte;
  km_write_iv : list byte;
  km_read_key : list byte;
  km_read_iv : list byte;
  km_hp_key : list byte
}.

Definition protect_packet (level : EncryptionLevel) (keys : KeyMaterial)
                         (header : list byte) (packet_number : word64)
                         (payload : list byte) : ProtectedPacket :=
  let aad := header in
  let ctx := {| aead_key := keys.(km_write_key);
                aead_iv := keys.(km_write_iv);
                aead_hp_key := keys.(km_hp_key) |} in
  let encrypted := aead_encrypt ctx payload aad packet_number in
  let sample := skipn 4 (firstn (4 + N.to_nat SAMPLE_LENGTH) encrypted) in
  let protected_header := apply_header_protection keys.(km_hp_key) sample header in
  {| pp_header := protected_header;
     pp_encrypted_pn := firstn 4 encrypted;
     pp_payload := encrypted |}.

Definition unprotect_packet (level : EncryptionLevel) (keys : KeyMaterial)
                           (packet : ProtectedPacket) : option (list byte * word64 * list byte) :=
  let sample := skipn 4 (firstn (4 + N.to_nat SAMPLE_LENGTH) packet.(pp_payload)) in
  let header := remove_header_protection keys.(km_hp_key) sample packet.(pp_header) in
  let packet_number := fold_left (fun acc b => N.lor (N.shiftl acc 8) b) 
                                 packet.(pp_encrypted_pn) 0 in
  let ctx := {| aead_key := keys.(km_read_key);
                aead_iv := keys.(km_read_iv);
                aead_hp_key := keys.(km_hp_key) |} in
  match aead_decrypt ctx packet.(pp_payload) header packet_number with
  | Some plaintext => Some (header, packet_number, plaintext)
  | None => None
  end.

(* =============================================================================
   Section 6: Key Update (RFC 9001 Section 6)
   ============================================================================= *)

Definition update_keys (current_secret : list byte) : list byte :=
  hkdf_expand_label current_secret "quic ku" 32.

Record KeyUpdateState := {
  ku_current_keys : KeyMaterial;
  ku_next_keys : option KeyMaterial;
  ku_key_phase : bool;
  ku_packets_sent : word64;
  ku_update_pending : bool
}.

Definition initiate_key_update (state : KeyUpdateState) : KeyUpdateState :=
  match state.(ku_next_keys) with
  | Some next =>
      {| ku_current_keys := next;
         ku_next_keys := None;
         ku_key_phase := negb state.(ku_key_phase);
         ku_packets_sent := 0;
         ku_update_pending := false |}
  | None => state
  end.

(* =============================================================================
   Section 7: Key Theorems  
   ============================================================================= *)

Theorem initial_secrets_deterministic : forall dcid1 dcid2,
  dcid1 = dcid2 ->
  derive_initial_secrets dcid1 = derive_initial_secrets dcid2.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Theorem key_update_toggles_phase : forall state next,
  state.(ku_next_keys) = Some next ->
  (initiate_key_update state).(ku_key_phase) = negb state.(ku_key_phase).
Proof.
  intros. unfold initiate_key_update.
  rewrite H. simpl. reflexivity.
Qed.

Theorem header_protection_involutive : forall hp_key sample header,
  Nat.le 5 (Datatypes.length header) ->
  remove_header_protection hp_key sample 
    (apply_header_protection hp_key sample header) = header.
Proof.
  intros. unfold remove_header_protection, apply_header_protection.
  destruct header as [|h0 header]; [simpl in H; inversion H|].
  destruct header as [|h1 header]; [simpl in H; inversion H; inversion H1|].
  destruct header as [|h2 header]; [simpl in H; inversion H; inversion H1; inversion H3|].
  destruct header as [|h3 header]; [simpl in H; inversion H; inversion H1; inversion H3; inversion H5|].
  destruct header as [|h4 header]; [simpl in H; inversion H; inversion H1; inversion H3; inversion H5; inversion H7|].
  simpl.
  (* The goal now shows XOR operations with the mask *)
  f_equal.
  - apply xor_byte_involutive.
  - (* For the remaining bytes, we need to show the XOR cancels *)
    set (mask := header_protection_mask hp_key sample).
    simpl.
    repeat f_equal; apply xor_byte_involutive.
Qed.

(* Missing RFC 9001 components:
   - Full TLS 1.3 handshake state machine
   - Retry packet integrity tag
   - 0-RTT data handling
   - Transport parameter negotiation
   - ALPN negotiation
   - Key schedule for all cipher suites
   - Packet number decoding/encoding
   - Stateless reset tokens *)
