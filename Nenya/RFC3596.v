(* =============================================================================
   Formal Verification of DNS Extensions to Support IP Version 6

   Specification: RFC 3596 (S. Thomson, C. Huitema, V. Ksinant, M. Souissi, October 2003)
   Target: DNS IPv6 Support

   Module: DNS IPv6 Extensions Formalization and Verification
   Author: Charles C Norton
   Date: September 1, 2025

   "For Annatar said: 'Let all things that are named be findable, wheresoever they may dwell.'"

   ============================================================================= *)

From Coq Require Import
  List
  NArith.NArith
  NArith.Nnat
  NArith.Ndiv_def
  Bool
  Arith
  Lia
  String
  Ascii.

Import ListNotations.
Open Scope N_scope.
Open Scope string_scope.

(* =============================================================================
   Section 1: Basic Types and Constants
   ============================================================================= *)

(* Type alias for 8-bit bytes (values 0..255) *)
Definition byte    := N.

(* Type alias for 16-bit words (values 0..65535) *)
Definition word16  := N.

(* Type alias for 32-bit words (modulo 2^32 enforced by [to_word32]) *)
Definition word32  := N.

(* IPv6 address as four 32-bit words (128 bits total) in network byte order *)
Definition word128 := (word32 * word32 * word32 * word32)%type.

(* Power-of-two helper: computes 2^k *)
Definition two (k:N) : N := N.pow 2 k.

(* Common powers of 2 for byte/word arithmetic *)
Definition two4  : N := two 4.   (* 16 - nibble bound *)
Definition two8  : N := two 8.   (* 256 - byte bound *)
Definition two16 : N := two 16.  (* 65536 - word16 bound *)
Definition two24 : N := two 24.  (* 16777216 - used in byte extraction *)
Definition two32 : N := two 32.  (* 4294967296 - word32 bound *)

(* Computational proofs that our power-of-two constants have expected values *)
Lemma two4_eq : two4 = 16. Proof. reflexivity. Qed.
Lemma two8_eq : two8 = 256. Proof. reflexivity. Qed.
Lemma two16_eq : two16 = 65536. Proof. reflexivity. Qed.
Lemma two24_eq : two24 = 16777216. Proof. reflexivity. Qed.
Lemma two32_eq : two32 = 4294967296. Proof. reflexivity. Qed.

(* Truncation functions: reduce arbitrary N to fit within type bounds via modulo *)
Definition to_byte   (x:N) : byte   := x mod two8.
Definition to_word16 (x:N) : word16 := x mod two16.
Definition to_word32 (x:N) : word32 := x mod two32.

(* If x already fits in a byte, truncation is identity *)
Lemma to_byte_small : forall x, x < two8 -> to_byte x = x.
Proof. intros x H; unfold to_byte; apply N.mod_small; exact H. Qed.

(* IPv6 DNS constants from RFC 3596 *)

(* AAAA record type code = 28 (RFC 3596 §2.1) *)
Definition AAAA_TYPE : word16 := 28.

(* PTR record type code = 12 (RFC 1035, used for reverse DNS) *)
Definition PTR_TYPE  : word16 := 12.

(* IN (Internet) class code = 1 *)
Definition IN_CLASS  : word16 := 1.

(* Standard suffix for IPv6 reverse DNS names (RFC 3596 §2.5) *)
Definition IP6_ARPA : list string := ["ip6"; "arpa"].

(* Historical/deprecated IPv6 reverse suffix; defined for completeness but not used *)
Definition IP6_INT  : list string := ["ip6"; "int"].

(* Compute the length of a string (number of characters) *)
Fixpoint strlen (s:string) : nat :=
  match s with
  | EmptyString => 0%nat
  | String _ tl => S (strlen tl)
  end.

(* Compute wire-format length of a domain name per RFC 1035:
   sum of (1 + label_length) for each label, plus 1 for the root's zero-length label.
   Example: "ip6.arpa" = (1+3) + (1+4) + 1 = 10 bytes *)
Definition domain_name_wire_len (labs:list string) : N :=
  N.of_nat (List.fold_right (fun s acc => S (strlen s) + acc)%nat 1%nat labs).

(* Truncate domain name wire length to 16-bit word (RFC 1035 limits names to 255 bytes) *)
Definition domain_name_length (labs:list string) : word16 :=
  to_word16 (domain_name_wire_len labs).

(* =============================================================================
   Section 2: AAAA Resource Record (RFC 3596 Section 2.1/2.2)
   ============================================================================= *)

(* Convert a 32-bit word to 4 bytes in big-endian (network) order.
   Example: 0x12345678 → [0x12, 0x34, 0x56, 0x78]
   Strategy: Extract bytes via division by powers of 256, then take mod 256 *)
Definition word32_to_bytes (w:word32) : list byte :=
  [ (w / two24) mod two8;   (* most significant byte *)
    (w / two16) mod two8;
    (w / two8 ) mod two8;
    w mod two8 ].           (* least significant byte *)

(* Reconstruct a 32-bit word from 4 bytes in big-endian order.
   Returns None if input is not exactly 4 bytes.
   Example: [0x12, 0x34, 0x56, 0x78] → Some 0x12345678 *)
Definition bytes_to_word32 (bs:list byte) : option word32 :=
  match bs with
  | [b0;b1;b2;b3] =>
      Some (to_word32 (b0 * two24 + b1 * two16 + b2 * two8 + b3))
  | _ => None
  end.

(* Serialize an IPv6 address (128-bit tuple) to 16 bytes in network order.
   An IPv6 address is represented as four 32-bit words (a,b,c,d).
   Each word is converted to 4 bytes, then concatenated: a || b || c || d *)
Definition ipv6_to_bytes (addr : word128) : list byte :=
  let '(a,b,c,d) := addr in
  word32_to_bytes a ++ word32_to_bytes b ++
  word32_to_bytes c ++ word32_to_bytes d.

(* Deserialize 16 bytes into an IPv6 address.
   Returns None unless input is exactly 16 bytes.
   Bytes are interpreted as four 32-bit words in network order. *)
Definition ipv6_from_bytes (bytes : list byte) : option word128 :=
  match bytes with
  | a0::a1::a2::a3::
    b0::b1::b2::b3::
    c0::c1::c2::c3::
    d0::d1::d2::d3::nil =>
      match bytes_to_word32 [a0;a1;a2;a3],
            bytes_to_word32 [b0;b1;b2;b3],
            bytes_to_word32 [c0;c1;c2;c3],
            bytes_to_word32 [d0;d1;d2;d3] with
      | Some a, Some b, Some c, Some d => Some (a,b,c,d)
      | _,_,_,_ => None
      end
  | _ => None
  end.

(* AAAA Resource Record structure per RFC 3596 §2.1-2.2.
   Fields match the DNS wire format:
   - name: domain name as list of labels
   - type: RR type (must be 28 for AAAA)
   - class: RR class (must be 1 for IN)
   - ttl: time-to-live in seconds
   - rdlength: RDATA length (must be 16 for AAAA)
   - address: 128-bit IPv6 address *)
Record AAAARecord := {
  aaaa_name     : list string;
  aaaa_type     : word16;         (* must be 28 *)
  aaaa_class    : word16;         (* must be IN (1) *)
  aaaa_ttl      : word32;
  aaaa_rdlength : word16;         (* must be 16 *)
  aaaa_address  : word128         (* 16 octets, network order *)
}.

(* Smart constructor that enforces RFC-mandated field values.
   Prevents construction of invalid AAAA records by automatically setting:
   - type = 28 (AAAA_TYPE)
   - class = 1 (IN_CLASS)
   - rdlength = 16 (fixed for all AAAA records) *)
Definition create_aaaa_record (name : list string) (addr : word128) (ttl : word32)
  : AAAARecord :=
  {| aaaa_name := name;
     aaaa_type := AAAA_TYPE;
     aaaa_class := IN_CLASS;
     aaaa_ttl := ttl;
     aaaa_rdlength := 16;
     aaaa_address := addr |}.

(* The smart constructor always produces records with rdlength = 16 *)
Lemma aaaa_fixed_size_create : forall name addr ttl,
  (create_aaaa_record name addr ttl).(aaaa_rdlength) = 16.
Proof. reflexivity. Qed.

(* Well-formedness predicate for validating AAAA records from untrusted sources.
   A record is well-formed if type=28, class=1, and rdlength=16. *)
Record AAAA_wf (r:AAAARecord) : Prop := {
  WF_type  : r.(aaaa_type) = AAAA_TYPE;
  WF_class : r.(aaaa_class) = IN_CLASS;
  WF_len   : r.(aaaa_rdlength) = 16
}.

(* Any well-formed AAAA record has rdlength = 16 *)
Theorem aaaa_fixed_size_wf : forall r, AAAA_wf r -> r.(aaaa_rdlength) = 16.
Proof. intros r H; exact (WF_len _ H). Qed.

(* =============================================================================
   Section 2b: AAAA RDATA Codec (RDATA = 16-octet IPv6 address)
   ============================================================================= *)

(* Encode an IPv6 address as 16 bytes of AAAA RDATA (RFC 3596 §2.2).
   This is the binary format stored in the RDATA field of an AAAA record. *)
Definition encode_AAAA_rdata (addr:word128) : list byte :=
  ipv6_to_bytes addr.

(* Decode 16 bytes of AAAA RDATA into an IPv6 address.
   Returns None if input is not exactly 16 bytes. *)
Definition decode_AAAA_rdata (bs:list byte) : option word128 :=
  ipv6_from_bytes bs.

(* Round-trip correctness proofs (encode ∘ decode = id) appear in Section 8c
   after we develop the necessary arithmetic and byte-manipulation lemmas. *)

(* =============================================================================
   Section 3: IPv6 Reverse Mapping (RFC 3596 Section 2.5)
   ============================================================================= *)

(* === Nibble (4-bit) Extraction from Bytes === *)

(* Extract the high nibble (upper 4 bits) of a byte.
   Example: hi_nib(0xAB) = 0xA = 10 *)
Definition hi_nib (b:byte) : N := (b / two4) mod two4.

(* Extract the low nibble (lower 4 bits) of a byte.
   Example: lo_nib(0xAB) = 0xB = 11 *)
Definition lo_nib (b:byte) : N := b mod two4.

(* The high nibble (b / 16) of any byte b < 256 is itself < 16.
   Proof strategy: Division by 16 reduces magnitude by factor of 16. *)
Lemma hi_nib_small : forall b, b < two8 -> (b / two4) < two4.
Proof.
  intros b Hb.
  unfold two8, two4, two in *.
  simpl in *.
  apply N.Div0.div_lt_upper_bound; lia.
Qed.

(* Any byte can be reconstructed from its quotient and remainder modulo 16:
   b = 16 * (b / 16) + (b mod 16)
   This is the division algorithm specialized to base-16. *)
Lemma byte_decompose : forall b, b < two8 -> two4 * (b / two4) + (b mod two4) = b.
Proof.
  intros b Hb.
  rewrite <- (N.div_mod b two4) at 1.
  - reflexivity.
  - unfold two4, two; simpl; lia.
Qed.

(* Combining high and low nibbles reconstructs the original byte.
   Proof: Unfold definitions and apply byte_decompose.
   This is a key lemma for proving nibble ↔ byte round-trips. *)
Lemma nibbles_reconstruct_byte : forall b,
  b < two8 -> to_byte (two4 * hi_nib b + lo_nib b) = b.
Proof.
  intros b Hb.
  unfold hi_nib, lo_nib.
  assert (Hdiv: b / two4 < two4) by (apply hi_nib_small; exact Hb).
  rewrite N.mod_small by exact Hdiv.
  rewrite byte_decompose by exact Hb.
  unfold to_byte.
  now rewrite N.mod_small.
Qed.

(* === Nibble ↔ DNS Label Conversion (for ip6.arpa names) === *)

(* Helper: create a single-character string from an ASCII character *)
Definition singleton (c:ascii) : string := String c EmptyString.

(* Convert a nibble (0-15) to its hexadecimal DNS label ("0".."9", "a".."f").
   Per RFC 3596 §2.5, nibbles in ip6.arpa names use lowercase hex.
   Example: nibble_label_of(10) = "a", nibble_label_of(15) = "f"
   Note: Exhaustive matching makes the inverse lemma trivial via vm_compute. *)
Definition nibble_label_of (n:N) : string :=
  match N.to_nat n with
  | 0%nat => "0"%string | 1%nat => "1"%string | 2%nat => "2"%string | 3%nat => "3"%string
  | 4%nat => "4"%string | 5%nat => "5"%string | 6%nat => "6"%string | 7%nat => "7"%string
  | 8%nat => "8"%string | 9%nat => "9"%string
  | 10%nat => "a"%string | 11%nat => "b"%string | 12%nat => "c"%string
  | 13%nat => "d"%string | 14%nat => "e"%string | 15%nat => "f"%string
  | _ => "0"%string (* unreachable for n<16 *)
  end.

(* Parse an ASCII character as a hexadecimal nibble (case-insensitive).
   Accepts:
   - '0'..'9' (ASCII 48-57) → 0..9
   - 'a'..'f' (ASCII 97-102) → 10..15
   - 'A'..'F' (ASCII 65-70) → 10..15
   Returns None for non-hex characters. *)
Definition ascii_to_nibble (c:ascii) : option N :=
  let n := nat_of_ascii c in
  if (48 <=? n)%nat && (n <=? 57)%nat then Some (N.of_nat (n - 48)%nat) else
  if (97 <=? n)%nat && (n <=? 102)%nat then Some (N.of_nat (n - 87)%nat) else
  if (65 <=? n)%nat && (n <=? 70)%nat then Some (N.of_nat (n - 55)%nat) else
  None.

(* Parse a single-character DNS label as a hexadecimal nibble.
   RFC 3596 §2.5 specifies ip6.arpa labels are single hex digits.
   Returns None if label is not exactly one character or not valid hex. *)
Definition label_to_nibble (s:string) : option N :=
  match s with
  | String c EmptyString => ascii_to_nibble c
  | _ => None
  end.

(* Any nibble n < 16 has N.to_nat(n) < 16.
   This bridges between Coq's N type and nat for exhaustive case analysis. *)
Lemma nibble_to_nat_bound : forall n,
  n < two4 -> (N.to_nat n < 16)%nat.
Proof.
  intros n H. unfold two4, two in H. simpl in H.
  repeat match goal with
  | H: N.succ _ < _ |- _ => apply N.lt_succ_r in H
  end.
  destruct n; cbn; lia.
Qed.

(* Round-trip property: nibble → label → nibble is identity.
   Proof: Exhaustive case analysis on all 16 possible nibbles (0..15).
   Each case verified via vm_compute on the definitions.
   This is a key correctness guarantee for ip6.arpa name generation. *)
Lemma label_of_nibble_inverse : forall n,
  n < two4 -> label_to_nibble (nibble_label_of n) = Some n.
Proof.
  intros n Hlt.
  unfold two4, two in Hlt. simpl in Hlt.
  destruct (N.eq_dec n 0); [subst; reflexivity|].
  destruct (N.eq_dec n 1); [subst; reflexivity|].
  destruct (N.eq_dec n 2); [subst; reflexivity|].
  destruct (N.eq_dec n 3); [subst; reflexivity|].
  destruct (N.eq_dec n 4); [subst; reflexivity|].
  destruct (N.eq_dec n 5); [subst; reflexivity|].
  destruct (N.eq_dec n 6); [subst; reflexivity|].
  destruct (N.eq_dec n 7); [subst; reflexivity|].
  destruct (N.eq_dec n 8); [subst; reflexivity|].
  destruct (N.eq_dec n 9); [subst; reflexivity|].
  destruct (N.eq_dec n 10); [subst; reflexivity|].
  destruct (N.eq_dec n 11); [subst; reflexivity|].
  destruct (N.eq_dec n 12); [subst; reflexivity|].
  destruct (N.eq_dec n 13); [subst; reflexivity|].
  destruct (N.eq_dec n 14); [subst; reflexivity|].
  destruct (N.eq_dec n 15); [subst; reflexivity|].
  lia.
Qed.

(* === Option List Utilities === *)

(* Convert a list of options into an option of a list (monadic sequence).
   Returns None if any element is None, otherwise Some of the unwrapped values.
   Example: sequence [Some 1; Some 2] = Some [1; 2]
            sequence [Some 1; None] = None *)
Fixpoint sequence {A} (xs:list (option A)) : option (list A) :=
  match xs with
  | [] => Some []
  | Some x :: tl => option_map (fun r => x::r) (sequence tl)
  | None :: _ => None
  end.

(* === Core Reverse DNS Conversion (RFC 3596 §2.5) === *)

(* Extract all nibbles from a byte list in ip6.arpa order.
   RFC 3596 §2.5: "low-order nibble is listed first", working backwards from last byte.

   Example: [0xAB, 0xCD] → rev([hi(0xAB); lo(0xAB); hi(0xCD); lo(0xCD)])
                          = [lo(0xCD); hi(0xCD); lo(0xAB); hi(0xAB)]
                          = [0xD, 0xC, 0xB, 0xA]

   Strategy: Extract nibbles in normal order, then reverse to match RFC. *)
Definition nibbles_rev_of_bytes (bs:list byte) : list N :=
  List.rev (List.flat_map (fun b => [hi_nib b; lo_nib b]) bs).

(* Prepending a byte adds its nibbles (reversed) to the end.
   Key property for inductive proofs about nibble extraction. *)
Lemma nibbles_rev_of_bytes_cons : forall b bs,
  nibbles_rev_of_bytes (b :: bs) =
  (nibbles_rev_of_bytes bs ++ [lo_nib b; hi_nib b])%list.
Proof.
  intros b bs. unfold nibbles_rev_of_bytes.
  cbn [List.flat_map List.rev List.app].
  repeat rewrite <- app_assoc. reflexivity.
Qed.

(* Appending a byte prepends its nibbles (reversed) to the result.
   Dual property to the cons lemma. *)
Lemma nibbles_rev_of_bytes_app : forall bs b,
  nibbles_rev_of_bytes (bs ++ [b]) =
  ([lo_nib b; hi_nib b] ++ nibbles_rev_of_bytes bs)%list.
Proof.
  intros bs b. unfold nibbles_rev_of_bytes.
  rewrite flat_map_app. simpl flat_map.
  rewrite rev_app_distr.
  simpl. reflexivity.
Qed.

(* Convert a list of nibbles to DNS labels (hex digit strings).
   Example: [10, 11, 12] → ["a", "b", "c"] *)
Definition labels_of_nibbles (ns:list N) : list string :=
  map nibble_label_of ns.

(* Parse a list of DNS labels as nibbles.
   Returns None if any label is invalid (not a single hex digit).
   Example: ["a", "b", "c"] → Some [10, 11, 12] *)
Definition nibbles_of_labels (ls:list string) : option (list N) :=
  sequence (map label_to_nibble ls).

(* If all nibbles are valid (<16), then labels → nibbles → labels is identity.
   Proof: Induction on nibble list, using label_of_nibble_inverse at each step.
   This guarantees that DNS labels faithfully represent nibble values. *)
Lemma labels_roundtrip_for_nibbles : forall ns,
  Forall (fun n => n < two4) ns ->
  nibbles_of_labels (labels_of_nibbles ns) = Some ns.
Proof.
  induction ns as [|n tl IH]; intro Hall; [reflexivity|].
  inversion Hall as [|? ? Hn Htl]; subst.
  unfold labels_of_nibbles, nibbles_of_labels in *. simpl.
  rewrite (label_of_nibble_inverse n Hn). simpl.
  now rewrite IH.
Qed.

(* === Reverse Conversion: Nibbles → Bytes === *)

(* Reconstruct bytes from nibbles in ip6.arpa order (pairs of lo, hi nibbles).
   Consumes nibbles two at a time: lo_nib, then hi_nib.
   Returns None if the nibble count is not even.

   Example: [0xD, 0xC, 0xB, 0xA] → Some [to_byte(16*0xC + 0xD), to_byte(16*0xA + 0xB)]
                                  = Some [0xCD, 0xAB]

   Note: This processes nibbles from the ip6.arpa end (low-order first). *)
Fixpoint bytes_from_nibbles_rev (ns:list N) : option (list byte) :=
  match ns with
  | [] => Some []
  | lo::hi::tl =>
      option_map (fun r => to_byte (two4*hi + lo) :: r) (bytes_from_nibbles_rev tl)
  | _ => None
  end.

(* Appending a nibble pair to the end produces the expected byte appended.
   Proof strategy: Structural induction using fix, handling all three cases
   (empty, singleton, pair+tail). *)
Lemma bytes_from_nibbles_rev_app : forall ns lo hi bs,
  bytes_from_nibbles_rev ns = Some bs ->
  bytes_from_nibbles_rev (ns ++ [lo; hi])%list =
    Some (bs ++ [to_byte (two4 * hi + lo)])%list.
Proof.
  fix IH 1.
  intros [|n1 [|n2 ns2]] lo hi bs H; simpl in *.
  - injection H as H; subst. reflexivity.
  - discriminate H.
  - destruct (bytes_from_nibbles_rev ns2) eqn:E; [|discriminate H].
    injection H as H; subst. simpl.
    specialize (IH ns2 lo hi l E).
    rewrite IH. reflexivity.
Qed.

(* Successful nibble→byte conversion produces exactly half as many bytes as nibbles.
   This length invariant is critical for ensuring 32 nibbles → 16 bytes. *)
Lemma bytes_from_nibbles_rev_length_ok :
  forall ns bytes,
    bytes_from_nibbles_rev ns = Some bytes ->
    List.length ns = (2 * List.length bytes)%nat.
Proof.
  fix IH 1.
  intros [|n1 [|n2 ns2]] bytes H; simpl in H.
  - injection H as H; subst. reflexivity.
  - discriminate H.
  - destruct (bytes_from_nibbles_rev ns2) eqn:E.
    + injection H as H; subst. simpl.
      specialize (IH ns2 l E). rewrite IH. lia.
    + discriminate H.
Qed.

(* Round-trip theorem: bytes → nibbles → bytes (in reverse order) is identity.
   This is one direction of the full ip6.arpa bijection proof.

   Proof strategy: Induction on byte list, using nibbles_reconstruct_byte
   to show that lo_nib and hi_nib correctly reconstruct each byte. *)
Lemma bytes_from_nibbles_rev_of_bytes :
  forall bs,
    Forall (fun b => b < two8) bs ->
    bytes_from_nibbles_rev (nibbles_rev_of_bytes bs) = Some (rev bs).
Proof.
  induction bs as [|b bs' IH]; intro Hall; [reflexivity|].
  inversion Hall as [|? ? Hb Hbs']; subst.
  rewrite nibbles_rev_of_bytes_cons.
  specialize (IH Hbs').
  assert (H_app: bytes_from_nibbles_rev (nibbles_rev_of_bytes bs' ++ [lo_nib b; hi_nib b])%list =
                 Some (rev bs' ++ [to_byte (two4 * hi_nib b + lo_nib b)])%list).
  { apply bytes_from_nibbles_rev_app. exact IH. }
  rewrite H_app. rewrite nibbles_reconstruct_byte by exact Hb.
  simpl. reflexivity.
Qed.

(* === Case-Insensitive DNS Label Comparison (RFC 1035 §2.3.3) === *)

(* Convert an ASCII uppercase letter (A-Z) to lowercase (a-z).
   ASCII codes: 'A'=65, 'Z'=90, 'a'=97, 'z'=122.
   Conversion: add 32 to uppercase letters, leave others unchanged. *)
Definition to_lower_ascii (c:ascii) : ascii :=
  let n := nat_of_ascii c in
  if (65 <=? n)%nat && (n <=? 90)%nat then ascii_of_nat (n + 32)%nat else c.

(* Convert an entire string to lowercase character-by-character. *)
Fixpoint to_lower (s:string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c tl => String (to_lower_ascii c) (to_lower tl)
  end.

(* Case-insensitive label equality check.
   Per RFC 1035, DNS labels are case-insensitive:
   "foo.com", "FOO.COM", and "Foo.Com" are all equivalent. *)
Definition eq_label_ci (a b:string) : bool :=
  String.eqb (to_lower a) (to_lower b).

(* If a label parses to nibble n, then nibble_label_of(n) is case-insensitively
   equal to the original label.
   Proof: Exhaustive vm_compute on all possible single-character hex labels. *)
Lemma nibble_label_roundtrip_ci : forall n lab,
  n < two4 ->
  label_to_nibble lab = Some n ->
  eq_label_ci (nibble_label_of n) lab = true.
Proof.
  intros n lab Hn Hlab.
  unfold label_to_nibble, ascii_to_nibble in Hlab.
  destruct lab as [|c []]; try discriminate.
  destruct c as [[] [] [] [] [] [] [] []]; vm_compute in Hlab |- *;
    try discriminate Hlab;
    injection Hlab as <-; reflexivity.
Qed.

(* === ip6.arpa Suffix Handling === *)

(* Remove the ".ip6.arpa" suffix from a domain name (case-insensitive).
   Returns Some(prefix) if the name ends with "ip6.arpa", None otherwise.

   Example: strip_ip6_arpa(["8", "b", "d", "0", "1", "0", "0", "2", "ip6", "arpa"])
            = Some ["8", "b", "d", "0", "1", "0", "0", "2"]

   Strategy: Reverse the label list to check suffix, then reverse result. *)
Definition strip_ip6_arpa (labs:list string) : option (list string) :=
  match rev labs with
  | a :: i :: rest_rev =>
      if andb (eq_label_ci a "arpa") (eq_label_ci i "ip6")
      then Some (rev rest_rev) else None
  | _ => None
  end.

(* === Main Public API: IPv6 ↔ Reverse DNS Conversion === *)

(* Convert an IPv6 address to its reverse DNS name (RFC 3596 §2.5).

   Algorithm:
   1. Serialize address to 16 bytes
   2. Extract all 32 nibbles in ip6.arpa order (low nibble of last byte first)
   3. Convert each nibble to a hex digit label
   4. Append ".ip6.arpa"

   Example: ::1 (0x00000000000000000000000000000001)
            → [... "1", "0", "0", ... "0", "ip6", "arpa"]
            = 1.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.ip6.arpa *)
Definition ipv6_to_reverse (addr : word128) : list string :=
  let bytes := ipv6_to_bytes addr in
  labels_of_nibbles (nibbles_rev_of_bytes bytes) ++ IP6_ARPA.

(* Decode a reverse DNS name back to an IPv6 address.
   Returns None if:
   - Name doesn't end with ".ip6.arpa" (case-insensitive)
   - Nibble count ≠ 32 (must represent exactly 128 bits)
   - Any label is not a valid hex digit

   Algorithm (inverse of ipv6_to_reverse):
   1. Strip and verify ".ip6.arpa" suffix
   2. Check that we have exactly 32 hex labels
   3. Parse labels as nibbles
   4. Reconstruct 16 bytes from nibble pairs
   5. Reverse byte order and deserialize to IPv6 address *)
Definition reverse_to_ipv6 (labs : list string) : option word128 :=
  match strip_ip6_arpa labs with
  | None => None
  | Some hexs =>
      if Nat.eqb (List.length hexs) 32%nat then
        match nibbles_of_labels hexs with
        | Some ns =>
            match bytes_from_nibbles_rev ns with
            | Some bytes_rev =>
                ipv6_from_bytes (rev bytes_rev)
            | None => None
            end
        | None => None
        end
      else None
  end.

(* === Arithmetic Foundations for word32 ↔ bytes Conversion === *)

(* All four bytes extracted from a word32 are valid (<256).
   This is immediate from the mod operation but crucial for type safety. *)
Lemma word32_to_bytes_bounds : forall w,
  Forall (fun b => b < two8) (word32_to_bytes w).
Proof.
  intro w; unfold word32_to_bytes.
  repeat constructor; apply N.mod_lt; unfold two8, two; simpl; lia.
Qed.

(* All 16 bytes of an IPv6 serialization are valid (<256). *)
Lemma ipv6_bytes_bounds : forall a b c d,
  Forall (fun x => x < two8) (ipv6_to_bytes (a,b,c,d)).
Proof.
  intros; unfold ipv6_to_bytes.
  repeat rewrite Forall_app; repeat split; apply word32_to_bytes_bounds.
Qed.

(* Individual byte extraction bounds (used in reconstruction proofs): *)

(* Byte 0 (most significant): (w / 2^24) mod 256 < 256 *)
Lemma word32_byte0_lt : forall w, w / two24 mod two8 < two8.
Proof. intros; apply N.mod_lt; unfold two8, two; simpl; lia. Qed.

(* Byte 1: (w / 2^16) mod 256 < 256 *)
Lemma word32_byte1_lt : forall w, w / two16 mod two8 < two8.
Proof. intros; apply N.mod_lt; unfold two8, two; simpl; lia. Qed.

(* Byte 2: (w / 2^8) mod 256 < 256 *)
Lemma word32_byte2_lt : forall w, w / two8 mod two8 < two8.
Proof. intros; apply N.mod_lt; unfold two8, two; simpl; lia. Qed.

(* Byte 3 (least significant): w mod 256 < 256 *)
Lemma word32_byte3_lt : forall w, w mod two8 < two8.
Proof. intros; apply N.mod_lt; unfold two8, two; simpl; lia. Qed.

(* === Modular Arithmetic Lemmas for Byte Extraction ===

   This section provides the algebraic foundation for proving that
   bytes_to_word32 ∘ word32_to_bytes is the identity (modulo 2^32).

   Key strategy: Show that nested mod operations collapse, and that
   division/mod commute in controlled ways. *)

(* If a < b, then a mod b = a (mod is identity for small values). *)
Lemma mod_small_iff : forall a b, b <> 0 -> a < b -> a mod b = a.
Proof. intros. apply N.mod_small. lia. Qed.

(* Result of mod is always strictly smaller than the modulus. *)
Lemma mod_of_mod_small : forall a b, b <> 0 -> a mod b < b.
Proof. intros. apply N.mod_lt. lia. Qed.

(* Adding multiples of the modulus doesn't change the remainder.
   (a + k*m) mod m = a mod m *)
Lemma add_mod_cancel_mult : forall a k m, m <> 0 -> (a + k * m) mod m = a mod m.
Proof.
  intros. apply N.Div0.mod_add; lia.
Qed.

(* Variant with multiplication on the left: (k*m + a) mod m = a mod m *)
Lemma add_mod_cancel_mult_l : forall a k m, m <> 0 -> (k * m + a) mod m = a mod m.
Proof.
  intros. replace (k * m + a) with (a + k * m) by lia.
  apply add_mod_cancel_mult. lia.
Qed.

(* Nested modulo collapse: (a mod (n*m)) mod m = a mod m
   Example: (x mod 65536) mod 256 = x mod 256
   This is crucial for showing byte extraction is consistent. *)
Lemma mod_mod_cancel : forall a n m,
  m <> 0 -> n <> 0 -> (a mod (n * m)) mod m = a mod m.
Proof.
  intros a n m Hm Hn.
  rewrite (N.div_mod a (n * m)) at 2 by lia.
  set (q := a / (n * m)).
  set (r := a mod (n * m)).
  replace (n * m * q) with ((n * q) * m) by lia.
  symmetry. apply add_mod_cancel_mult_l. lia.
Qed.

(* Concrete instantiation: (w mod 65536) mod 256 = w mod 256
   Used for extracting the least significant byte. *)
Lemma mod256_of_mod65536 : forall w,
  (w mod 65536) mod 256 = w mod 256.
Proof.
  intros. replace 65536 with (256 * 256) by lia.
  apply mod_mod_cancel; lia.
Qed.

(* Division with additive offset: (k*m + a) / m = k + (a / m)
   The k*m term contributes exactly k to the quotient. *)
Lemma div_add_cancel : forall a k m, m <> 0 -> (k * m + a) / m = k + a / m.
Proof.
  intros. replace (k * m + a) with (a + k * m) by lia.
  rewrite N.div_add by lia. lia.
Qed.

(* Division and modulo swap for nested operations:
   (a mod (n*m)) / m = (a / m) mod n

   Intuition: Taking a mod (n*m) keeps the lower (log₂(n*m)) bits.
   Dividing by m then shifts right by log₂(m) bits.
   The result is the middle log₂(n) bits, which is (a/m) mod n.

   This is the key lemma for multi-level byte extraction. *)
Lemma div_mod_swap : forall a n m,
  m <> 0 -> n <> 0 -> (a mod (n * m)) / m = a / m mod n.
Proof.
  intros a n m Hm Hn.
  set (q := a / (n * m)).
  set (r := a mod (n * m)).
  assert (Ea: a = n * m * q + r).
  { unfold q, r. apply N.div_mod. lia. }
  rewrite Ea.
  replace (n * m * q) with ((n * q) * m) by lia.
  rewrite div_add_cancel by lia.
  replace (n * q) with (q * n) by lia.
  replace (q * n + r / m) with (r / m + q * n) by lia.
  rewrite N.Div0.mod_add by lia.
  symmetry. apply N.mod_small.
  unfold r.
  replace (n * m) with (m * n) by lia.
  apply N.Div0.div_lt_upper_bound; try apply N.mod_lt; lia.
Qed.

(* Concrete instantiation: (w mod 65536) / 256 = (w / 256) mod 256
   Used for extracting byte 1 (second-least significant byte). *)
Lemma div256_of_mod65536 : forall w,
  (w mod 65536) / 256 = w / 256 mod 256.
Proof.
  intros. replace 65536 with (256 * 256) by lia.
  apply div_mod_swap; lia.
Qed.

(* Similar lemma for next power: (w mod 2^24) mod 2^16 = w mod 2^16 *)
Lemma mod65536_of_mod16777216 : forall w,
  (w mod 16777216) mod 65536 = w mod 65536.
Proof.
  intros. replace 16777216 with (256 * 65536) by lia.
  apply mod_mod_cancel; lia.
Qed.

(* Extract byte 2: (w mod 2^24) / 2^16 = (w / 2^16) mod 256 *)
Lemma div65536_of_mod16777216 : forall w,
  (w mod 16777216) / 65536 = w / 65536 mod 256.
Proof.
  intros. replace 16777216 with (256 * 65536) by lia.
  apply div_mod_swap; lia.
Qed.

(* If w < 2^32, then w / 2^24 < 256 (most significant byte fits). *)
Lemma div16777216_lt256 : forall w, w < 4294967296 -> w / 16777216 < 256.
Proof. intros. apply N.Div0.div_lt_upper_bound; lia. Qed.

(* Generalized div/mod compatibility with nested modulo. *)
Lemma div_mod_compat_256 : forall w d,
  d <> 0 -> 256 <> 0 ->
  w / d mod 256 = (w mod (256 * d)) / d mod 256.
Proof.
  intros w d Hd H256.
  rewrite div_mod_swap by lia.
  rewrite N.Div0.mod_mod by lia.
  reflexivity.
Qed.

(* === Word32 Byte Reconstruction (proving decode ∘ encode = id) ===

   These lemmas hierarchically decompose a 32-bit word into its 4 bytes,
   proving that the extraction strategy in word32_to_bytes is reversible. *)

(* Step 1: Split into byte0 (most significant) and lower 24 bits.
   w = byte0 * 2^24 + (w mod 2^24) *)
Lemma byte_reconstruction_step1 : forall w,
  w < 4294967296 ->
  w = (w / 16777216) * 16777216 + w mod 16777216.
Proof.
  intros.
  rewrite N.mul_comm.
  apply N.div_mod. lia.
Qed.

(* Step 2: Split lower 24 bits into byte1 and lower 16 bits.
   (w mod 2^24) = byte1 * 2^16 + (w mod 2^16) *)
Lemma byte_reconstruction_step2 : forall w,
  w mod 16777216 = (w / 65536 mod 256) * 65536 + w mod 65536.
Proof.
  intros.
  rewrite (N.div_mod (w mod 16777216) 65536) at 1 by lia.
  rewrite div65536_of_mod16777216, mod65536_of_mod16777216.
  rewrite N.mul_comm.
  reflexivity.
Qed.

(* Step 3: Split lower 16 bits into byte2 and byte3.
   (w mod 2^16) = byte2 * 2^8 + byte3 *)
Lemma byte_reconstruction_step3 : forall w,
  w mod 65536 = (w / 256 mod 256) * 256 + w mod 256.
Proof.
  intros.
  rewrite (N.div_mod (w mod 65536) 256) at 1 by lia.
  rewrite div256_of_mod65536, mod256_of_mod65536.
  rewrite N.mul_comm.
  reflexivity.
Qed.

(* === Byte Extraction Commutes with word32 Truncation ===

   These lemmas show that extracting bytes from an arbitrary N value
   gives the same result as extracting from (N mod 2^32).
   This is crucial for proving to_word32 normalizes correctly. *)

(* Byte 3 (LSB) extraction commutes with to_word32 truncation. *)
Lemma mod_256_of_mod_2_32 : forall w,
  w mod 256 = (w mod 4294967296) mod 256.
Proof.
  intros. replace 4294967296 with (16777216 * 256) by lia.
  symmetry. apply mod_mod_cancel; lia.
Qed.

(* Byte 2 extraction commutes with to_word32 truncation. *)
Lemma div_256_mod_256_of_mod_2_32 : forall w,
  w / 256 mod 256 = (w mod 4294967296) / 256 mod 256.
Proof.
  intros.
  replace 4294967296 with (16777216 * 256) by lia.
  rewrite div_mod_swap by lia.
  replace 16777216 with (65536 * 256) by lia.
  symmetry. apply mod_mod_cancel; lia.
Qed.

(* Byte 1 extraction commutes with to_word32 truncation. *)
Lemma div_65536_mod_256_of_mod_2_32 : forall w,
  w / 65536 mod 256 = (w mod 4294967296) / 65536 mod 256.
Proof.
  intros.
  replace 4294967296 with (65536 * 65536) by lia.
  rewrite div_mod_swap by lia.
  replace 65536 with (256 * 256) by lia.
  symmetry. apply mod_mod_cancel; lia.
Qed.

(* Double modulo is idempotent: (a mod m) mod m = a mod m *)
Lemma mod_mod_same : forall a m, m <> 0 -> (a mod m) mod m = a mod m.
Proof.
  intros. apply N.mod_small. apply N.mod_lt. assumption.
Qed.

(* Byte 0 (MSB) extraction commutes with to_word32 truncation. *)
Lemma div_16777216_mod_256_of_mod_2_32 : forall w,
  w / 16777216 mod 256 = (w mod 4294967296) / 16777216 mod 256.
Proof.
  intros. replace 4294967296 with (256 * 16777216) by lia.
  rewrite div_mod_swap by lia.
  symmetry. apply mod_mod_same. lia.
Qed.

(* === Convenient Restatements for Each Byte === *)

(* These lemmas are convenient restatements of the above commutation properties. *)

(* Byte 3 (LSB) equality under truncation *)
Lemma byte0_eq : forall w, w mod 256 = (w mod 4294967296) mod 256.
Proof. intros. apply mod_256_of_mod_2_32. Qed.

(* Byte 2 equality under truncation *)
Lemma byte1_eq : forall w, w / 256 mod 256 = (w mod 4294967296) / 256 mod 256.
Proof. intros. apply div_256_mod_256_of_mod_2_32. Qed.

(* Byte 1 equality under truncation *)
Lemma byte2_eq : forall w, w / 65536 mod 256 = (w mod 4294967296) / 65536 mod 256.
Proof. intros. apply div_65536_mod_256_of_mod_2_32. Qed.

(* Byte 0 (MSB) equality under truncation *)
Lemma byte3_eq : forall w, w / 16777216 mod 256 = (w mod 4294967296) / 16777216 mod 256.
Proof. intros. apply div_16777216_mod_256_of_mod_2_32. Qed.

(* If w fits in 32 bits, its MSB fits in 8 bits *)
Lemma byte3_normalized : forall w, w < 4294967296 -> w / 16777216 < 256.
Proof. intros. apply div16777216_lt256. assumption. Qed.

(* For normalized word32, MSB extraction doesn't need mod *)
Lemma byte3_mod_small : forall w, w < 4294967296 -> w / 16777216 mod 256 = w / 16777216.
Proof. intros. apply N.mod_small. apply byte3_normalized. assumption. Qed.

(* === Main Word32 Reconstruction Theorem ===

   Combining the extracted bytes via the standard formula reconstructs
   the original word (for values < 2^32).

   This is the algebraic heart of the bytes_to_word32 ∘ word32_to_bytes
   round-trip proof. *)

Lemma w32_from_bytes : forall w, w < 4294967296 ->
  w / 16777216 * 16777216 +
  (w / 65536 mod 256 * 65536 +
   (w / 256 mod 256 * 256 + w mod 256)) = w.
Proof.
  intros w Hw.
  assert (H1: w = w / 16777216 * 16777216 + w mod 16777216).
  { apply byte_reconstruction_step1. exact Hw. }
  assert (H2: w mod 16777216 = (w / 65536 mod 256) * 65536 + w mod 65536).
  { apply byte_reconstruction_step2. }
  assert (H3: w mod 65536 = (w / 256 mod 256) * 256 + w mod 256).
  { apply byte_reconstruction_step3. }
  rewrite H2 in H1. rewrite H3 in H1. symmetry. exact H1.
Qed.

(* Reconstruction theorem with symbolic constants (two8, two16, etc.).
   This is the same as w32_from_bytes but with abstract notation.

   Proof strategy: Reduce symbolic constants to concrete numbers, then
   apply the byte commutation lemmas and w32_from_bytes. *)

Lemma word32_reconstruction : forall w,
  (w / two24 mod two8) * two24 +
  (w / two16 mod two8) * two16 +
  (w / two8 mod two8) * two8 +
  (w mod two8) = w mod two32.
Proof.
  intro w. rewrite two24_eq, two16_eq, two8_eq, two32_eq.
  set (w' := w mod 4294967296).
  assert (Hw': w' < 4294967296) by (apply N.mod_lt; lia).
  assert (E0: w mod 256 = w' mod 256) by (apply byte0_eq).
  assert (E1: w / 256 mod 256 = w' / 256 mod 256) by (apply byte1_eq).
  assert (E2: w / 65536 mod 256 = w' / 65536 mod 256) by (apply byte2_eq).
  assert (E3: w / 16777216 mod 256 = w' / 16777216 mod 256) by (apply byte3_eq).
  rewrite E0, E1, E2, E3.
  rewrite (byte3_mod_small w' Hw').
  replace (w' / 16777216 * 16777216 + w' / 65536 mod 256 * 65536 + w' / 256 mod 256 * 256 + w' mod 256)
    with (w' / 16777216 * 16777216 + (w' / 65536 mod 256 * 65536 + (w' / 256 mod 256 * 256 + w' mod 256))) by lia.
  apply w32_from_bytes. exact Hw'.
Qed.

(* Truncating the reconstructed byte sum equals truncating the original.
   This shows to_word32 commutes with byte reconstruction. *)

Lemma to_word32_of_bytes_eq : forall w,
  to_word32 ((w / two24 mod two8) * two24 +
             (w / two16 mod two8) * two16 +
             (w / two8 mod two8) * two8 +
             (w mod two8)) = to_word32 w.
Proof.
  intro w. unfold to_word32.
  rewrite word32_reconstruction.
  apply N.Div0.mod_mod; unfold two32, two; simpl; lia.
Qed.

(* word32 to bytes and back preserves value (modulo 2^32).
   Foundation for AAAA RDATA codec correctness. *)

Lemma word32_bytes_roundtrip : forall w,
  bytes_to_word32 (word32_to_bytes w) = Some (to_word32 w).
Proof.
  intro w. unfold word32_to_bytes, bytes_to_word32, to_word32.
  repeat rewrite N.mod_small by (apply word32_byte0_lt || apply word32_byte1_lt ||
                                  apply word32_byte2_lt || apply word32_byte3_lt).
  f_equal. rewrite word32_reconstruction. assert (H: two32 <> 0) by (unfold two32, two; simpl; lia).
  rewrite N.Div0.mod_mod by exact H. reflexivity.
Qed.

(* === Byte Extraction from Reconstructed Word (Reverse Direction) ===

   These lemmas prove that extracting bytes from a reconstructed word32
   yields the original bytes. This is the other half of the round-trip proof. *)

(* Four valid bytes (<256) combine to a valid word32 (<2^32).
   Proof: Maximum value is 255*2^24 + 255*2^16 + 255*2^8 + 255 = 4294967295 < 2^32 *)

Lemma byte_sum_lt_word32 : forall b0 b1 b2 b3,
  b0 < two8 -> b1 < two8 -> b2 < two8 -> b3 < two8 ->
  b0 * two24 + b1 * two16 + b2 * two8 + b3 < two32.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3.
  unfold two8, two24, two16, two32, two in *. simpl in *.
  assert (Hmax: b0 * 16777216 + b1 * 65536 + b2 * 256 + b3 <= 255 * 16777216 + 255 * 65536 + 255 * 256 + 255).
  { repeat apply N.add_le_mono; try apply N.mul_le_mono_nonneg_l; lia. }
  apply N.le_lt_trans with (m := 255 * 16777216 + 255 * 65536 + 255 * 256 + 255).
  - exact Hmax.
  - lia.
Qed.

(* Extract byte 0 (MSB) from reconstructed word: isolating the b0 coefficient.
   Formula: (b0*2^24 + lower_bits) / 2^24 mod 256 = b0

   Proof strategy:
   1. Show lower_bits < 2^24 (so they don't contribute to quotient)
   2. Use division distributivity: (a + k*m) / m = k + a/m
   3. Since lower_bits / 2^24 = 0, we get b0 + 0 = b0
   4. Apply mod 256, which is identity since b0 < 256 *)

Lemma byte0_extract : forall b0 b1 b2 b3,
  b0 < two8 -> b1 < two8 -> b2 < two8 -> b3 < two8 ->
  (b0 * two24 + b1 * two16 + b2 * two8 + b3) / two24 mod two8 = b0.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3.
  unfold two8, two24, two16, two in *. simpl in *.
  assert (Hsmall: b1 * 65536 + b2 * 256 + b3 < 16777216).
  { assert (Hmax: b1 * 65536 + b2 * 256 + b3 <= 255 * 65536 + 255 * 256 + 255).
    { repeat apply N.add_le_mono; try apply N.mul_le_mono_nonneg_l; lia. }
    apply N.le_lt_trans with (m := 255 * 65536 + 255 * 256 + 255).
    - exact Hmax.
    - lia. }
  assert (E: (b0 * 16777216 + b1 * 65536 + b2 * 256 + b3) / 16777216 mod 256 = b0).
  { replace (b0 * 16777216 + b1 * 65536 + b2 * 256 + b3)
      with ((b1 * 65536 + b2 * 256 + b3) + b0 * 16777216) by ring.
    rewrite N.div_add by lia.
    rewrite N.div_small by exact Hsmall.
    rewrite N.add_0_l.
    apply N.mod_small. lia. }
  exact E.
Qed.

(* Extract byte 1 from reconstructed word: isolating the b1 coefficient.
   Formula: (b0*2^24 + b1*2^16 + lower_bits) / 2^16 mod 256 = b1

   Proof strategy:
   1. Rewrite as (lower_bits + (b0*256 + b1) * 2^16) to isolate b1's contribution
   2. Division: lower_bits / 2^16 = 0, leaving (b0*256 + b1)
   3. Modulo 256 cancels b0's contribution: (b0*256 + b1) mod 256 = b1 *)

Lemma byte1_extract : forall b0 b1 b2 b3,
  b0 < two8 -> b1 < two8 -> b2 < two8 -> b3 < two8 ->
  (b0 * two24 + b1 * two16 + b2 * two8 + b3) / two16 mod two8 = b1.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3.
  unfold two8, two24, two16, two in *. simpl in *.
  assert (Hsmall: b2 * 256 + b3 < 65536).
  { assert (Hmax: b2 * 256 + b3 <= 255 * 256 + 255).
    { repeat apply N.add_le_mono; try apply N.mul_le_mono_nonneg_l; lia. }
    apply N.le_lt_trans with (m := 255 * 256 + 255).
    - exact Hmax.
    - lia. }
  assert (E: (b0 * 16777216 + b1 * 65536 + b2 * 256 + b3) / 65536 mod 256 = b1).
  { assert (Eq: b0 * 16777216 + b1 * 65536 + b2 * 256 + b3 =
                 (b2 * 256 + b3) + (b0 * 256 + b1) * 65536) by ring.
    rewrite Eq.
    rewrite N.div_add by lia.
    rewrite N.div_small by exact Hsmall.
    simpl.
    assert (Hmod: (b0 * 256 + b1) mod 256 = b1).
    { replace (b0 * 256 + b1) with (b1 + b0 * 256) by ring.
      rewrite N.Div0.mod_add by lia.
      apply N.mod_small. lia. }
    exact Hmod. }
  exact E.
Qed.

(* Extract byte 2 from reconstructed word: isolating the b2 coefficient.
   Formula: (higher_bits + b2*2^8 + b3) / 2^8 mod 256 = b2

   Proof strategy:
   1. Rewrite as b3 + (b0*65536 + b1*256 + b2) * 256
   2. Division: b3 / 256 = 0, leaving (b0*65536 + b1*256 + b2)
   3. Modulo 256: Higher terms (b0*65536, b1*256) are multiples of 256, so mod = 0
   4. Result: b2 *)

Lemma byte2_extract : forall b0 b1 b2 b3,
  b0 < two8 -> b1 < two8 -> b2 < two8 -> b3 < two8 ->
  (b0 * two24 + b1 * two16 + b2 * two8 + b3) / two8 mod two8 = b2.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3.
  unfold two8, two24, two16, two in *. simpl in *.
  assert (Hsmall: b3 < 256) by exact H3.
  assert (E: (b0 * 16777216 + b1 * 65536 + b2 * 256 + b3) / 256 mod 256 = b2).
  { assert (Eq: b0 * 16777216 + b1 * 65536 + b2 * 256 + b3 =
                 b3 + (b0 * 65536 + b1 * 256 + b2) * 256) by ring.
    rewrite Eq.
    rewrite N.div_add by lia.
    rewrite N.div_small by exact Hsmall.
    simpl.
    assert (Hmod: (b0 * 65536 + b1 * 256 + b2) mod 256 = b2).
    { rewrite (N.Div0.add_mod (b0 * 65536 + b1 * 256) b2) by lia.
      rewrite (N.Div0.add_mod (b0 * 65536) (b1 * 256)) by lia.
      assert (E1: b0 * 65536 mod 256 = 0).
      { replace (b0 * 65536) with ((b0 * 256) * 256) by ring.
        rewrite N.Div0.mod_mul by lia. reflexivity. }
      assert (E2: b1 * 256 mod 256 = 0).
      { replace (b1 * 256) with (b1 * 256) by ring.
        rewrite N.Div0.mod_mul by lia. reflexivity. }
      rewrite E1, E2.
      simpl.
      rewrite N.Div0.mod_mod by lia.
      apply N.mod_small. lia. }
    exact Hmod. }
  exact E.
Qed.

(* Extract byte 3 (LSB) from reconstructed word: isolating the b3 coefficient.
   Formula: (higher_bits + b3) mod 256 = b3

   Proof strategy:
   1. All higher terms (b0*2^24, b1*2^16, b2*2^8) are multiples of 256
   2. Their sum mod 256 = 0
   3. Therefore (higher_bits + b3) mod 256 = (0 + b3) mod 256 = b3
   4. Since b3 < 256, final mod is identity *)

Lemma byte3_extract : forall b0 b1 b2 b3,
  b0 < two8 -> b1 < two8 -> b2 < two8 -> b3 < two8 ->
  (b0 * two24 + b1 * two16 + b2 * two8 + b3) mod two8 = b3.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3.
  unfold two8, two24, two16, two in *. simpl in *.
  assert (E: (b0 * 16777216 + b1 * 65536 + b2 * 256 + b3) mod 256 = b3).
  { rewrite (N.Div0.add_mod (b0 * 16777216 + b1 * 65536 + b2 * 256) b3) by lia.
    assert (E0: (b0 * 16777216 + b1 * 65536 + b2 * 256) mod 256 = 0).
    { rewrite (N.Div0.add_mod (b0 * 16777216 + b1 * 65536) (b2 * 256)) by lia.
      assert (E1: (b0 * 16777216 + b1 * 65536) mod 256 = 0).
      { rewrite (N.Div0.add_mod (b0 * 16777216) (b1 * 65536)) by lia.
        assert (E2: b0 * 16777216 mod 256 = 0).
        { replace (b0 * 16777216) with ((b0 * 65536) * 256) by ring.
          rewrite N.Div0.mod_mul by lia. reflexivity. }
        assert (E3: b1 * 65536 mod 256 = 0).
        { replace (b1 * 65536) with ((b1 * 256) * 256) by ring.
          rewrite N.Div0.mod_mul by lia. reflexivity. }
        rewrite E2, E3. reflexivity. }
      assert (E4: b2 * 256 mod 256 = 0).
      { replace (b2 * 256) with (b2 * 256) by ring.
        rewrite N.Div0.mod_mul by lia. reflexivity. }
      rewrite E1, E4. reflexivity. }
    rewrite E0.
    rewrite N.add_0_l.
    rewrite N.Div0.mod_mod by lia.
    apply N.mod_small. lia. }
  exact E.
Qed.

(* Reconstructing a word32 from bytes and extracting bytes yields originals.
   Combined with word32_bytes_roundtrip, proves bijection between word32 and bytes.
   Proof applies byte0_extract through byte3_extract. *)

Lemma bytes_word32_roundtrip : forall b0 b1 b2 b3,
  b0 < two8 -> b1 < two8 -> b2 < two8 -> b3 < two8 ->
  word32_to_bytes (to_word32 (b0 * two24 + b1 * two16 + b2 * two8 + b3)) = [b0; b1; b2; b3].
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3.
  unfold word32_to_bytes, to_word32.
  assert (Hlt: b0 * two24 + b1 * two16 + b2 * two8 + b3 < two32).
  { apply byte_sum_lt_word32; assumption. }
  assert (Heq: (b0 * two24 + b1 * two16 + b2 * two8 + b3) mod two32 =
                b0 * two24 + b1 * two16 + b2 * two8 + b3).
  { apply N.mod_small. exact Hlt. }
  rewrite Heq.
  repeat (f_equal; try reflexivity).
  - apply byte0_extract; assumption.
  - apply byte1_extract; assumption.
  - apply byte2_extract; assumption.
  - apply byte3_extract; assumption.
Qed.

(* === IPv6 Address Normalization ===

   Since word32 components are represented as arbitrary N values but semantically
   should be in range [0, 2^32), we define normalization that truncates each
   component modulo 2^32. *)

Definition normalize128 (ip:word128) : word128 :=
  let '(a,b,c,d) := ip in (to_word32 a, to_word32 b, to_word32 c, to_word32 d).

(* === Case-Insensitive Label Equality Properties === *)

(* Lowercasing an already-lowercase "arpa" is identity *)
Lemma to_lower_lowercase_arpa : to_lower "arpa" = "arpa".
Proof. reflexivity. Qed.

(* Lowercasing "ARPA" yields "arpa" *)
Lemma to_lower_uppercase_arpa : to_lower "ARPA" = "arpa".
Proof. reflexivity. Qed.

(* Lowercasing "ip6" is identity *)
Lemma to_lower_lowercase_ip6 : to_lower "ip6" = "ip6".
Proof. reflexivity. Qed.

(* Lowercasing "IP6" yields "ip6" *)
Lemma to_lower_uppercase_ip6 : to_lower "IP6" = "ip6".
Proof. reflexivity. Qed.

(* Case-insensitive equality is reflexive *)
Lemma eq_label_ci_refl : forall s, eq_label_ci s s = true.
Proof.
  intro s. unfold eq_label_ci.
  rewrite String.eqb_refl. reflexivity.
Qed.

(* Case-insensitive equality iff lowercase forms are equal *)
Lemma eq_label_ci_lower : forall s t,
  eq_label_ci s t = true <-> to_lower s = to_lower t.
Proof.
  intros s t. unfold eq_label_ci.
  apply String.eqb_eq.
Qed.

(* Case-insensitive equality is symmetric *)
Lemma eq_label_ci_sym : forall s t,
  eq_label_ci s t = eq_label_ci t s.
Proof.
  intros s t. unfold eq_label_ci.
  destruct (String.eqb (to_lower s) (to_lower t)) eqn:E.
  - apply String.eqb_eq in E. symmetry in E.
    apply String.eqb_eq in E. rewrite E. reflexivity.
  - destruct (String.eqb (to_lower t) (to_lower s)) eqn:E2; [|reflexivity].
    apply String.eqb_eq in E2. symmetry in E2.
    apply String.eqb_eq in E2. rewrite E2 in E. discriminate.
Qed.

(* Case-insensitive equality is transitive *)
Lemma eq_label_ci_trans : forall r s t,
  eq_label_ci r s = true -> eq_label_ci s t = true -> eq_label_ci r t = true.
Proof.
  intros r s t H1 H2.
  apply eq_label_ci_lower in H1.
  apply eq_label_ci_lower in H2.
  apply eq_label_ci_lower.
  rewrite H1. exact H2.
Qed.

Require Import Coq.Classes.RelationClasses.

(* Case-insensitive equality forms an equivalence relation.
   This allows using it in rewriting and other Coq automation. *)
Instance eq_label_ci_Equivalence : Equivalence (fun s t => eq_label_ci s t = true).
Proof.
  split.
  - intros x. apply eq_label_ci_refl.
  - intros x y H. rewrite eq_label_ci_sym. exact H.
  - intros x y z. apply eq_label_ci_trans.
Qed.

(* === Suffix Stripping Lemmas === *)

(* Stripping ".ip6.arpa" from a name ending with it yields the prefix.
   This is a key property for the reverse DNS round-trip proof. *)
Lemma strip_ip6_arpa_app_hex :
  forall hexs, strip_ip6_arpa (hexs ++ IP6_ARPA) = Some hexs.
Proof.
  intro hexs; unfold strip_ip6_arpa, IP6_ARPA, eq_label_ci.
  rewrite rev_app_distr; cbn.
  now rewrite rev_involutive.
Qed.

(* strip_ip6_arpa is case-insensitive: "IP6.ARPA" works too *)
Lemma strip_ip6_arpa_case_insensitive :
  forall hexs, strip_ip6_arpa (hexs ++ ["IP6"; "ARPA"]) = Some hexs.
Proof.
  intro hexs; unfold strip_ip6_arpa, eq_label_ci.
  rewrite rev_app_distr; cbn.
  now rewrite rev_involutive.
Qed.

(* === Length Invariants for Reverse DNS Conversion === *)

(* Extracting nibbles from N bytes yields 2*N nibbles.
   This is fundamental for ensuring 16 bytes → 32 nibbles. *)
Lemma nibbles_rev_of_bytes_length : forall bs,
  List.length (nibbles_rev_of_bytes bs) = (2 * List.length bs)%nat.
Proof.
  induction bs as [|b tl IH]; [reflexivity|].
  rewrite nibbles_rev_of_bytes_cons.
  rewrite app_length, IH. simpl. lia.
Qed.

(* word32_to_bytes always produces exactly 4 bytes *)
Lemma word32_to_bytes_length : forall w,
  List.length (word32_to_bytes w) = 4%nat.
Proof. intros; reflexivity. Qed.

(* IPv6 serialization always produces exactly 16 bytes (4 words × 4 bytes) *)
Lemma ipv6_to_bytes_length : forall a b c d,
  List.length (ipv6_to_bytes (a,b,c,d)) = 16%nat.
Proof.
  intros; unfold ipv6_to_bytes.
  repeat rewrite app_length.
  now rewrite !word32_to_bytes_length.
Qed.

(* All nibbles extracted from bytes are valid (< 16).
   This is because hi_nib and lo_nib both apply mod 16. *)
Lemma nibbles_rev_of_bytes_bounds :
  forall bs, Forall (fun n => n < two4) (nibbles_rev_of_bytes bs).
Proof.
  induction bs as [|b tl IH]; [constructor|].
  rewrite nibbles_rev_of_bytes_cons.
  rewrite Forall_app; split; [assumption|].
  repeat constructor; apply N.mod_lt; unfold two4, two; simpl; lia.
Qed.

(* IPv6 address to reverse DNS name and back yields normalized address.
   Main correctness guarantee for RFC 3596 §2.5.

   Proof outline:
   1. ipv6_to_reverse produces nibble_labels ++ ".ip6.arpa"
   2. Strip suffix with strip_ip6_arpa_app_hex
   3. Verify 32 nibble labels (16 bytes × 2 nibbles/byte)
   4. Parse labels to nibbles (labels_roundtrip_for_nibbles)
   5. Reconstruct bytes from nibbles (bytes_from_nibbles_rev_of_bytes)
   6. Reverse byte list to restore original order
   7. Deserialize to IPv6 (word32_bytes_roundtrip per word)
   8. Result equals normalize128(ip) by to_word32_of_bytes_eq *)

Theorem reverse_roundtrip_normalized :
  forall ip, reverse_to_ipv6 (ipv6_to_reverse ip) = Some (normalize128 ip).
Proof.
  intros [[[a b] c] d].
  unfold ipv6_to_reverse, reverse_to_ipv6.
  set (bytes := ipv6_to_bytes (a,b,c,d)).
  set (ns := nibbles_rev_of_bytes bytes).
  set (hexs := labels_of_nibbles ns).
  rewrite strip_ip6_arpa_app_hex.
  assert (Hlen: List.length hexs = 32%nat).
  { subst hexs ns bytes.
    unfold labels_of_nibbles.
    rewrite map_length, nibbles_rev_of_bytes_length, ipv6_to_bytes_length.
    reflexivity. }
  rewrite Hlen. simpl.
  assert (Hnib: Forall (fun n => n < two4) ns).
  { subst ns. apply nibbles_rev_of_bytes_bounds. }
  subst hexs.
  rewrite (labels_roundtrip_for_nibbles ns Hnib).
  assert (Hbytes: Forall (fun x => x < two8) bytes).
  { subst bytes. apply ipv6_bytes_bounds. }
  subst ns.
  rewrite (bytes_from_nibbles_rev_of_bytes bytes Hbytes).
  subst bytes.
  rewrite rev_involutive.
  unfold ipv6_to_bytes, ipv6_from_bytes.
  repeat rewrite word32_bytes_roundtrip.
  unfold normalize128. simpl.
  f_equal. f_equal. f_equal. f_equal.
  - apply to_word32_of_bytes_eq.
  - apply to_word32_of_bytes_eq.
  - apply to_word32_of_bytes_eq.
  - apply to_word32_of_bytes_eq.
Qed.

(* === Well-Formedness for IPv6 Addresses ===

   An IPv6 address is well-formed if each 32-bit component is actually
   within the range [0, 2^32). This ensures no overflow/truncation occurs. *)

Definition wf_ipv6 (ip:word128) : Prop :=
  let '(a,b,c,d) := ip in a < two32 /\ b < two32 /\ c < two32 /\ d < two32.

(* If x is already less than 2^32, truncation is identity *)
Lemma to_word32_id_if_lt : forall x, x < two32 -> to_word32 x = x.
Proof. intros x H; unfold to_word32; apply N.mod_small; exact H. Qed.

(* For well-formed IPv6 addresses (all components < 2^32), reverse DNS
   round-trip is exact—no normalization needed.
   ipv6_to_reverse and reverse_to_ipv6 are perfect inverses on well-formed inputs. *)

Theorem reverse_bijective :
  forall ip, wf_ipv6 ip -> reverse_to_ipv6 (ipv6_to_reverse ip) = Some ip.
Proof.
  intros [[[a b] c] d] [Ha [Hb [Hc Hd]]].
  rewrite reverse_roundtrip_normalized.
  unfold normalize128.
  now rewrite !to_word32_id_if_lt.
Qed.

(* === Case-Insensitive List Equality ===

   Extend case-insensitive comparison to lists of labels.
   Two domain names are equal if all corresponding labels match
   case-insensitively. *)

Fixpoint list_eq_ci (xs ys : list string) : bool :=
  match xs, ys with
  | [], [] => true
  | x::xs', y::ys' => andb (eq_label_ci x y) (list_eq_ci xs' ys')
  | _, _ => false
  end.

(* list_eq_ci is reflexive *)
Lemma list_eq_ci_refl : forall xs, list_eq_ci xs xs = true.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  simpl. rewrite eq_label_ci_refl, IH. reflexivity.
Qed.

(* list_eq_ci distributes over list append.
   If xs1 ≈ ys1 and xs2 ≈ ys2, then (xs1++xs2) ≈ (ys1++ys2). *)
Lemma list_eq_ci_app : forall xs1 xs2 ys1 ys2,
  list_eq_ci xs1 ys1 = true ->
  list_eq_ci xs2 ys2 = true ->
  list_eq_ci (xs1 ++ xs2) (ys1 ++ ys2) = true.
Proof.
  induction xs1 as [|x xs1 IH]; intros xs2 ys1 ys2 H1 H2.
  - destruct ys1; [exact H2|discriminate].
  - destruct ys1 as [|y ys1]; [discriminate|].
    simpl in H1. apply andb_prop in H1. destruct H1 as [Hx Hxs].
    simpl. rewrite Hx. apply IH; assumption.
Qed.

(* If two nibbles are equal, their label representations are case-insensitively equal.
   (Trivial since they map to the same label.) *)
Lemma nibble_label_of_ci : forall n m,
  n < two4 -> m < two4 -> n = m -> eq_label_ci (nibble_label_of n) (nibble_label_of m) = true.
Proof.
  intros n m Hn Hm Heq. subst. apply eq_label_ci_refl.
Qed.

(* Equal nibble lists produce case-insensitively equal label lists *)
Lemma labels_of_nibbles_ci : forall ns ms,
  ns = ms ->
  list_eq_ci (labels_of_nibbles ns) (labels_of_nibbles ms) = true.
Proof.
  intros ns ms Heq. subst. apply list_eq_ci_refl.
Qed.

(* === Helper Lemmas for Option List Processing === *)

(* If sequence succeeds, the result has the same length as the input *)
Lemma sequence_map_length : forall {A} (f : string -> option A) (ls : list string) (res : list A),
  sequence (map f ls) = Some res ->
  List.length res = List.length ls.
Proof.
  intros A f.
  induction ls as [|l ls IH]; intros res H; simpl in H.
  - injection H as H. subst. reflexivity.
  - destruct (f l) eqn:E; [|discriminate].
    destruct (sequence (map f ls)) eqn:E2; [|discriminate].
    injection H as H. subst. simpl. f_equal. apply IH. reflexivity.
Qed.

(* Parsing labels as nibbles preserves length *)
Lemma nibbles_of_labels_length : forall labs ns,
  nibbles_of_labels labs = Some ns ->
  List.length ns = List.length labs.
Proof.
  intros labs ns H. unfold nibbles_of_labels in H.
  now apply sequence_map_length in H.
Qed.

(* === Bounds Preservation Through Nibble/Byte Conversion === *)

(* If nibbles successfully convert to bytes, all bytes are valid (<256).
   This follows from the to_byte call in bytes_from_nibbles_rev. *)
Lemma bytes_from_nibbles_rev_some_forall : forall ns bytes,
  bytes_from_nibbles_rev ns = Some bytes ->
  Forall (fun b => b < two8) bytes.
Proof.
  fix IH 1.
  intros ns bytes H.
  destruct ns as [|n1 [|n2 ns2]]; simpl in H.
  - injection H as H. subst. constructor.
  - discriminate.
  - destruct (bytes_from_nibbles_rev ns2) eqn:E; [|discriminate].
    injection H as H. subst. constructor.
    + apply N.mod_lt. unfold two8, two. simpl. lia.
    + apply (IH ns2). exact E.
Qed.

(* If 16 valid bytes successfully deserialize to an IPv6 address,
   the resulting address is well-formed (all components < 2^32).

   This is because bytes_to_word32 applies to_word32, which enforces
   the mod 2^32 bound. *)
Lemma ipv6_from_bytes_some_bounds : forall bytes ip,
  ipv6_from_bytes bytes = Some ip ->
  Forall (fun b => b < two8) bytes ->
  wf_ipv6 ip.
Proof.
  intros bytes [[[a b] c] d] H Hbounds.
  unfold ipv6_from_bytes in H.
  destruct bytes as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 [|b9 [|b10 [|b11 [|b12 [|b13 [|b14 [|b15 rest]]]]]]]]]]]]]]]]; try discriminate.
  destruct rest; [|discriminate].
  simpl in H.
  injection H as Ha Hb Hc Hd. subst a b c d.
  unfold wf_ipv6. simpl.
  repeat split; unfold to_word32; apply N.mod_lt; unfold two32, two; simpl; lia.
Qed.


(* === Nibble Pair Reconstruction (Reverse Direction) === *)

(* Two valid nibbles combine to a valid byte: 16*n2 + n1 < 256
   Maximum: 16*15 + 15 = 255 < 256 *)
Lemma nibble_pair_sum_lt : forall n1 n2,
  n1 < two4 -> n2 < two4 -> two4 * n2 + n1 < two8.
Proof.
  intros n1 n2 Hn1 Hn2.
  unfold two8, two4, two in *.
  simpl in *.
  assert (Hmax: 16 * n2 + n1 <= 15 * 16 + 15).
  { repeat apply N.add_le_mono; try apply N.mul_le_mono_nonneg_l; lia. }
  apply N.le_lt_trans with (m := 15 * 16 + 15); [exact Hmax|].
  vm_compute. reflexivity.
Qed.

(* Extracting the low nibble from a reconstructed byte yields the original low nibble.
   Formula: lo_nib(to_byte(16*n2 + n1)) = n1

   Proof: Since 16*n2 + n1 < 256, to_byte is identity. Then modulo 16 isolates n1. *)
Lemma lo_nib_of_pair : forall n1 n2,
  n1 < two4 -> n2 < two4 ->
  lo_nib (to_byte (two4 * n2 + n1)) = n1.
Proof.
  intros n1 n2 Hn1 Hn2.
  unfold lo_nib, to_byte.
  assert (Hsum: two4 * n2 + n1 < two8) by (apply nibble_pair_sum_lt; assumption).
  rewrite (N.mod_small (two4 * n2 + n1) two8) by exact Hsum.
  replace (two4 * n2 + n1) with (n1 + n2 * two4) by lia.
  rewrite N.Div0.mod_add by (unfold two4, two; simpl; lia).
  apply N.mod_small. exact Hn1.
Qed.

(* Extracting the high nibble from a reconstructed byte yields the original high nibble.
   Formula: hi_nib(to_byte(16*n2 + n1)) = n2

   Proof: Division by 16 isolates n2, then mod 16 is identity since n2 < 16. *)
Lemma hi_nib_of_pair : forall n1 n2,
  n1 < two4 -> n2 < two4 ->
  hi_nib (to_byte (two4 * n2 + n1)) = n2.
Proof.
  intros n1 n2 Hn1 Hn2.
  unfold hi_nib, to_byte.
  assert (Hsum: two4 * n2 + n1 < two8) by (apply nibble_pair_sum_lt; assumption).
  rewrite (N.mod_small (two4 * n2 + n1) two8) by exact Hsum.
  replace (two4 * n2 + n1) with (n1 + n2 * two4) by lia.
  rewrite N.div_add by (unfold two4, two; simpl; lia).
  rewrite (N.div_small n1 two4) by exact Hn1.
  simpl. apply N.mod_small. exact Hn2.
Qed.

(* === Nibbles ↔ Bytes Round-Trip (Reverse Direction) ===

   If nibbles successfully convert to bytes, extracting nibbles from those
   bytes (in reverse order) yields the original nibbles.

   This is the other half of the nibble/byte bijection proof.

   Proof strategy: Structural induction on nibbles (pairs at a time).
   Use lo_nib_of_pair and hi_nib_of_pair to show each byte reconstructs
   its two nibbles correctly. *)

Lemma nibbles_bytes_roundtrip : forall ns bytes,
  bytes_from_nibbles_rev ns = Some bytes ->
  Forall (fun n => n < two4) ns ->
  nibbles_rev_of_bytes (rev bytes) = ns.
Proof.
  fix IH 1.
  intros ns bytes H Hnib.
  destruct ns as [|n1 [|n2 ns2]]; simpl in H.
  - injection H as H. subst. reflexivity.
  - discriminate.
  - inversion Hnib as [|? ? Hn1 [|? ? Hn2 Hns2]]; subst.
    destruct (bytes_from_nibbles_rev ns2) eqn:E; [|discriminate].
    injection H as H. subst.
    assert (IHres: nibbles_rev_of_bytes (rev l0) = ns2).
    { apply (IH ns2). exact E. exact Hns2. }
    simpl rev.
    transitivity ([lo_nib (to_byte (two4 * n2 + n1)); hi_nib (to_byte (two4 * n2 + n1))] ++ ns2)%list.
    { rewrite nibbles_rev_of_bytes_app. f_equal. exact IHres. }
    rewrite (lo_nib_of_pair n1 n2 Hn1 Hn2).
    rewrite (hi_nib_of_pair n1 n2 Hn1 Hn2).
    reflexivity.
Qed.

(* === Labels ↔ Nibbles Round-Trip (Reverse Direction, Case-Insensitive) ===

   If labels successfully parse to nibbles, converting those nibbles back
   to labels yields case-insensitively equal labels.

   This completes the label ↔ nibble bijection (up to case).

   Proof: Induction on labels, using nibble_label_roundtrip_ci at each step. *)

Lemma labels_nibbles_roundtrip_ci : forall labs ns,
  nibbles_of_labels labs = Some ns ->
  Forall (fun n => n < two4) ns ->
  list_eq_ci (labels_of_nibbles ns) labs = true.
Proof.
  induction labs as [|lab labs IH]; intros ns H Hnib.
  - simpl in H. injection H as H. subst. reflexivity.
  - unfold nibbles_of_labels in H. simpl in H.
    remember (label_to_nibble lab) as olab.
    destruct olab as [n|]; [|discriminate H].
    symmetry in Heqolab. rename Heqolab into Elab.
    remember (sequence (map label_to_nibble labs)) as olabs.
    destruct olabs as [ns'|]; [|discriminate H].
    symmetry in Heqolabs. rename Heqolabs into Eseq.
    injection H as H. subst ns.
    inversion Hnib as [|? ? Hn Hns']; subst.
    simpl. unfold labels_of_nibbles. simpl.
    assert (Hci: eq_label_ci (nibble_label_of n) lab = true).
    { apply nibble_label_roundtrip_ci; assumption. }
    rewrite Hci.
    apply IH.
    + unfold nibbles_of_labels. exact Eseq.
    + exact Hns'.
Qed.

(* === Equivalence Lemma: Reverse DNS Pipeline ===

   The reverse DNS round-trip is equivalent to the direct byte serialization
   round-trip. This bridges the two perspectives.

   Proof: Mechanically unfold both sides and show they follow the same
   pipeline through nibbles and bytes. *)

Lemma reverse_bytes_pipeline_equiv :
  forall ip,
    reverse_to_ipv6 (ipv6_to_reverse ip) =
    ipv6_from_bytes (ipv6_to_bytes ip).
Proof.
  intros [[[a b] c] d].
  unfold ipv6_to_reverse, reverse_to_ipv6.
  set (bytes := ipv6_to_bytes (a,b,c,d)).
  set (ns := nibbles_rev_of_bytes bytes).
  set (hexs := labels_of_nibbles ns).
  rewrite strip_ip6_arpa_app_hex.
  assert (Hlen: List.length hexs = 32%nat).
  { subst hexs ns bytes.
    unfold labels_of_nibbles.
    rewrite map_length, nibbles_rev_of_bytes_length, ipv6_to_bytes_length.
    reflexivity. }
  rewrite Hlen. simpl.
  assert (Hnib: Forall (fun n => n < two4) ns).
  { subst ns. apply nibbles_rev_of_bytes_bounds. }
  subst hexs.
  rewrite (labels_roundtrip_for_nibbles ns Hnib).
  assert (Hbytes: Forall (fun x => x < two8) bytes).
  { subst bytes. apply ipv6_bytes_bounds. }
  subst ns.
  rewrite (bytes_from_nibbles_rev_of_bytes bytes Hbytes).
  subst bytes.
  now rewrite rev_involutive.
Qed.

(* IPv6 address to bytes and back yields normalized address.
   Derived from reverse_roundtrip_normalized via equivalence lemma. *)

Theorem ipv6_bytes_roundtrip :
  forall ip, ipv6_from_bytes (ipv6_to_bytes ip) = Some (normalize128 ip).
Proof.
  intro ip.
  pose proof (reverse_roundtrip_normalized ip) as H.
  rewrite (reverse_bytes_pipeline_equiv ip) in H.
  exact H.
Qed.

(* For well-formed addresses, byte serialization is a perfect bijection.
   Practical guarantee: valid IPv6 addresses survive serialization. *)

Theorem ipv6_bytes_roundtrip_wf :
  forall ip, wf_ipv6 ip -> ipv6_from_bytes (ipv6_to_bytes ip) = Some ip.
Proof.
  intros ip Hwf.
  rewrite ipv6_bytes_roundtrip.
  destruct ip as [[[a b] c] d]; simpl in *.
  unfold normalize128.
  destruct Hwf as [Ha [Hb [Hc Hd]]].
  now rewrite !to_word32_id_if_lt.
Qed.

Theorem ipv6_to_reverse_converse : forall ip labs,
  reverse_to_ipv6 labs = Some ip ->
  list_eq_ci (ipv6_to_reverse ip) labs = true.
Proof.
  intros ip labs H.
  unfold reverse_to_ipv6 in H.
  destruct (strip_ip6_arpa labs) as [hexs|] eqn:Estrip; [|discriminate].
  destruct (Nat.eqb (List.length hexs) 32) eqn:Elen; [|discriminate].
  destruct (nibbles_of_labels hexs) as [ns|] eqn:Enib; [|discriminate].
  destruct (bytes_from_nibbles_rev ns) as [bytes_rev|] eqn:Ebytes; [|discriminate].
  destruct (ipv6_from_bytes (rev bytes_rev)) as [ip'|] eqn:Eip; [|discriminate].
  injection H as H. subst ip'.
  unfold ipv6_to_reverse.
  unfold strip_ip6_arpa in Estrip.
  destruct (rev labs) as [|a [|i rest_rev]] eqn:Erev; [discriminate|discriminate|].
  destruct (andb (eq_label_ci a "arpa") (eq_label_ci i "ip6")) eqn:Eand; [|discriminate].
  injection Estrip as Estrip. subst hexs.
  apply andb_prop in Eand. destruct Eand as [Ha Hi].
  rewrite <- (rev_involutive labs).
  rewrite Erev.
  change (rev (a :: i :: rest_rev)) with ((rev (i :: rest_rev)) ++ [a])%list.
  change (rev (i :: rest_rev)) with ((rev rest_rev) ++ [i])%list.
  rewrite <- app_assoc.
  apply list_eq_ci_app.
  - assert (Hbytes_bounds: Forall (fun b => b < two8) bytes_rev).
    { apply bytes_from_nibbles_rev_some_forall in Ebytes. exact Ebytes. }
    assert (Hnib_len: List.length ns = List.length (rev rest_rev)).
    { apply nibbles_of_labels_length in Enib. exact Enib. }
    apply Nat.eqb_eq in Elen.
    assert (Hlen_ns: List.length ns = 32%nat).
    { rewrite Hnib_len. exact Elen. }
    assert (Hlen_bytes: List.length bytes_rev = 16%nat).
    { apply bytes_from_nibbles_rev_length_ok in Ebytes.
      rewrite Hlen_ns in Ebytes. lia. }
    assert (Hnib_bounds: Forall (fun n => n < two4) ns).
    { clear -Enib.
      unfold nibbles_of_labels in Enib.
      enough (forall labs res, sequence (map label_to_nibble labs) = Some res -> Forall (fun n => n < two4) res) by (apply (H _ _ Enib)).
      intros labs. induction labs as [|l ls IH]; intros res H; simpl in H.
      - injection H as <-. constructor.
      - destruct (label_to_nibble l) eqn:E; [|discriminate].
        destruct (sequence (map label_to_nibble ls)) as [l0|] eqn:E2; [|discriminate].
        injection H as <-.
        assert (Hl0: Forall (fun n => n < two4) l0) by (apply (IH _ eq_refl)).
        constructor; [|exact Hl0].
        unfold label_to_nibble in E.
        destruct l as [|a []]; try discriminate.
        unfold ascii_to_nibble in E.
        destruct a as [[] [] [] [] [] [] [] []]; vm_compute in E |- *;
          try discriminate E;
          injection E as <-; vm_compute; constructor. }
    assert (Hip_wf: wf_ipv6 ip).
    { apply ipv6_from_bytes_some_bounds with (bytes := rev bytes_rev).
      - exact Eip.
      - apply Forall_rev. exact Hbytes_bounds. }
    set (ip_bytes := ipv6_to_bytes ip).
    assert (Hip_bytes_eq: ipv6_from_bytes ip_bytes = Some ip).
    { subst ip_bytes. apply ipv6_bytes_roundtrip_wf. exact Hip_wf. }
    assert (Hbytes_eq: ip_bytes = rev bytes_rev).
    { subst ip_bytes.
      assert (Heq1: ipv6_from_bytes (rev bytes_rev) = Some ip) by exact Eip.
      assert (Heq2: ipv6_from_bytes (ipv6_to_bytes ip) = Some ip).
      { apply ipv6_bytes_roundtrip_wf. exact Hip_wf. }
      remember (rev bytes_rev) as bytes_fwd eqn:E1.
      assert (Hlen_fwd: List.length bytes_fwd = 16%nat).
      { rewrite E1, rev_length. exact Hlen_bytes. }
      destruct bytes_fwd as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 [|b9 [|b10 [|b11 [|b12 [|b13 [|b14 [|b15 rest]]]]]]]]]]]]]]]];
        try discriminate Hlen_fwd.
      destruct rest as [|? ?]; [|discriminate Hlen_fwd].
      assert (Hbounds_fwd: Forall (fun b => b < two8) [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15]).
      { rewrite E1. apply Forall_rev. exact Hbytes_bounds. }
      clear Hlen_bytes Hlen_fwd Hbytes_bounds Heq2.
      inversion Hbounds_fwd as [|? ? Eb0 H0]; clear Hbounds_fwd; subst.
      inversion H0 as [|? ? Eb1 H1]; clear H0; subst.
      inversion H1 as [|? ? Eb2 H2]; clear H1; subst.
      inversion H2 as [|? ? Eb3 H3]; clear H2; subst.
      inversion H3 as [|? ? Eb4 H4]; clear H3; subst.
      inversion H4 as [|? ? Eb5 H5]; clear H4; subst.
      inversion H5 as [|? ? Eb6 H6]; clear H5; subst.
      inversion H6 as [|? ? Eb7 H7]; clear H6; subst.
      inversion H7 as [|? ? Eb8 H8]; clear H7; subst.
      inversion H8 as [|? ? Eb9 H9]; clear H8; subst.
      inversion H9 as [|? ? Eb10 H10]; clear H9; subst.
      inversion H10 as [|? ? Eb11 H11]; clear H10; subst.
      inversion H11 as [|? ? Eb12 H12]; clear H11; subst.
      inversion H12 as [|? ? Eb13 H13]; clear H12; subst.
      inversion H13 as [|? ? Eb14 H14]; clear H13; subst.
      inversion H14 as [|? ? Eb15 H15]; clear H14; subst.
      clear H15.
      unfold ipv6_from_bytes in Heq1.
      destruct ip as [[[wa wb] wc] wd].
      injection Heq1 as Ewa Ewb Ewc Ewd. subst wa wb wc wd.
      unfold ipv6_to_bytes.
      rewrite (bytes_word32_roundtrip b0 b1 b2 b3 Eb0 Eb1 Eb2 Eb3).
      rewrite (bytes_word32_roundtrip b4 b5 b6 b7 Eb4 Eb5 Eb6 Eb7).
      rewrite (bytes_word32_roundtrip b8 b9 b10 b11 Eb8 Eb9 Eb10 Eb11).
      rewrite (bytes_word32_roundtrip b12 b13 b14 b15 Eb12 Eb13 Eb14 Eb15).
      reflexivity. }
    rewrite Hbytes_eq.
    rewrite (nibbles_bytes_roundtrip ns bytes_rev Ebytes Hnib_bounds).
    apply labels_nibbles_roundtrip_ci.
    + exact Enib.
    + exact Hnib_bounds.
  - unfold IP6_ARPA. simpl list_eq_ci.
    rewrite eq_label_ci_sym. rewrite Hi. simpl.
    rewrite eq_label_ci_sym. rewrite Ha. simpl.
    reflexivity.
Qed.

(* =============================================================================
   Section 3b: Additional-Section Processing (RFC 3596 Section 3)
   ============================================================================= *)

(* RFC 3596 §3: NS, SRV, MX queries that perform additional-section processing
   MUST include both A and AAAA glue when available. We capture just the rule. *)

Inductive rrtype := RT_A | RT_AAAA | RT_NS | RT_SRV | RT_MX | RT_PTR | RT_OTHER.

Definition needs_additional (qt:rrtype) : bool :=
  match qt with RT_NS | RT_SRV | RT_MX => true | _ => false end.

Definition additional_glue (qt:rrtype) : list rrtype :=
  if needs_additional qt then [RT_A; RT_AAAA] else [].

Lemma additional_contains_AAAA_when_needed :
  forall qt, needs_additional qt = true -> In RT_AAAA (additional_glue qt).
Proof. intros [] H; simpl in *; try discriminate; auto. Qed.

(* =============================================================================
   Section 4: Dual Stack Considerations (kept lightweight; advisory)
   ============================================================================= *)

Record DualStackConfig := {
  ds_prefer_ipv6 : bool;
  ds_ipv6_only   : bool;
  ds_ipv4_only   : bool
}.

Inductive QueryStrategy :=
  | QS_AAAA_ONLY
  | QS_A_ONLY
  | QS_AAAA_THEN_A
  | QS_PARALLEL.

Definition determine_strategy (config : DualStackConfig) : QueryStrategy :=
  if config.(ds_ipv6_only) then QS_AAAA_ONLY
  else if config.(ds_ipv4_only) then QS_A_ONLY
  else if config.(ds_prefer_ipv6) then QS_AAAA_THEN_A
  else QS_PARALLEL.

(* =============================================================================
   Section 5: Transport Selection (informational; AAAA itself doesn't change DNS transport)
   ============================================================================= *)

Record IPv6Transport := {
  t6_has_ipv6 : bool;
  t6_has_ipv4 : bool
}.

Inductive TransportChoice := UseIPv6 | UseIPv4.

Definition select_transport (transport : IPv6Transport)
                            (has_aaaa has_a : bool) : option TransportChoice :=
  if andb has_aaaa transport.(t6_has_ipv6) then Some UseIPv6
  else if andb has_a transport.(t6_has_ipv4) then Some UseIPv4
  else None.

(* =============================================================================
   Section 6: Transition Mechanisms (notes)
   ============================================================================= *)

(* A6 is historic; ip6.int deprecated — retained as constants only. *)
Definition A6_TYPE : word16 := 38.

(* =============================================================================
   Section 7: IPv6 Address Selection (notes)
   ============================================================================= *)
(* Not part of RFC 3596 proper; omitted here for focus. *)

(* =============================================================================
   Section 8a: Auxiliary Length/Bound Lemmas and DNS Name Invariants
   ============================================================================= *)

Lemma ipv6_to_reverse_has_suffix :
  forall ip, exists hexs : list string,
    ipv6_to_reverse ip = (hexs ++ IP6_ARPA)%list /\ List.length hexs = 32%nat.
Proof.
  intros [[[a b] c] d]; unfold ipv6_to_reverse.
  set (bytes := ipv6_to_bytes (a,b,c,d)).
  exists (labels_of_nibbles (nibbles_rev_of_bytes bytes)).
  split; [reflexivity|].
  unfold labels_of_nibbles.
  rewrite map_length, nibbles_rev_of_bytes_length.
  subst bytes. rewrite ipv6_to_bytes_length. lia.
Qed.

Lemma ipv6_to_reverse_label_count :
  forall ip, List.length (ipv6_to_reverse ip) = 34%nat.
Proof.
  intro ip. destruct (ipv6_to_reverse_has_suffix ip) as [hexs [H S]].
  rewrite H, app_length. unfold IP6_ARPA. simpl length. rewrite S. reflexivity.
Qed.

Lemma strlen_nibble_label_of :
  forall n, n < two4 -> strlen (nibble_label_of n) = 1%nat.
Proof.
  intros n Hlt.
  unfold two4, two in Hlt. simpl in Hlt.
  destruct (N.eq_dec n 0); [subst; reflexivity|].
  destruct (N.eq_dec n 1); [subst; reflexivity|].
  destruct (N.eq_dec n 2); [subst; reflexivity|].
  destruct (N.eq_dec n 3); [subst; reflexivity|].
  destruct (N.eq_dec n 4); [subst; reflexivity|].
  destruct (N.eq_dec n 5); [subst; reflexivity|].
  destruct (N.eq_dec n 6); [subst; reflexivity|].
  destruct (N.eq_dec n 7); [subst; reflexivity|].
  destruct (N.eq_dec n 8); [subst; reflexivity|].
  destruct (N.eq_dec n 9); [subst; reflexivity|].
  destruct (N.eq_dec n 10); [subst; reflexivity|].
  destruct (N.eq_dec n 11); [subst; reflexivity|].
  destruct (N.eq_dec n 12); [subst; reflexivity|].
  destruct (N.eq_dec n 13); [subst; reflexivity|].
  destruct (N.eq_dec n 14); [subst; reflexivity|].
  destruct (N.eq_dec n 15); [subst; reflexivity|].
  lia.
Qed.

Lemma labels_of_nibbles_all_len1 :
  forall ns,
    Forall (fun n => n < two4) ns ->
    Forall (fun s => strlen s = 1%nat) (labels_of_nibbles ns).
Proof.
  induction ns as [|n tl IH]; intro Hall; simpl; [constructor|].
  inversion Hall as [|? ? Hn Htl]; subst.
  constructor.
  - now apply strlen_nibble_label_of.
  - now apply IH.
Qed.

Definition wire_acc (s:string) (acc:nat) : nat := S (strlen s) + acc.

Lemma fold_right_constant_len :
  forall xs base,
    Forall (fun s => strlen s = 1%nat) xs ->
    fold_right wire_acc base xs = (base + 2 * List.length xs)%nat.
Proof.
  induction xs as [|x xs IH]; cbn; intros base Hall; [lia|].
  inversion Hall as [|? ? Hx Hxs]; subst.
  rewrite Hx, IH by assumption. lia.
Qed.

Lemma wire_base_suffix_ip6_arpa :
  fold_right wire_acc 1%nat IP6_ARPA = 10%nat.
Proof.
  unfold IP6_ARPA, wire_acc. simpl fold_right. simpl strlen. reflexivity.
Qed.

Definition label_ok (s:string) : Prop := (strlen s <= 63)%nat.
Definition name_ok (labs:list string) : Prop :=
  (domain_name_wire_len labs <= 255)%N /\ Forall label_ok labs.

Lemma map_length_eq : forall {A B} (f : A -> B) (l : list A),
  List.length (map f l) = List.length l.
Proof.
  intros A B f l. apply map_length.
Qed.

Lemma fold_right_wire_acc_hexs : forall hexs,
  Forall (fun s => strlen s = 1%nat) hexs ->
  fold_right wire_acc 10%nat hexs = (10 + 2 * List.length hexs)%nat.
Proof.
  intros hexs H. apply fold_right_constant_len. exact H.
Qed.

Lemma ipv6_reverse_name_ok :
  forall ip, name_ok (ipv6_to_reverse ip).
Proof.
  intros [[[a b] c] d]; unfold ipv6_to_reverse, name_ok.
  set (bytes := ipv6_to_bytes (a,b,c,d)).
  set (ns := nibbles_rev_of_bytes bytes).
  set (hexs := labels_of_nibbles ns).
  split.
  - unfold domain_name_wire_len.
    subst hexs.
    assert (Hlen_bytes : List.length bytes = 16%nat)
      by (apply ipv6_to_bytes_length).
    assert (Hlen_ns : List.length ns = 32%nat).
    { subst ns. rewrite nibbles_rev_of_bytes_length, Hlen_bytes. reflexivity. }
    assert (Hlen_hexs : List.length (labels_of_nibbles ns) = 32%nat).
    { unfold labels_of_nibbles. rewrite map_length_eq. exact Hlen_ns. }
    assert (Hnib : Forall (fun n => n < two4) ns)
      by (apply nibbles_rev_of_bytes_bounds).
    assert (Hall1 : Forall (fun s => strlen s = 1%nat) (labels_of_nibbles ns))
      by (apply labels_of_nibbles_all_len1; exact Hnib).
    change (N.of_nat (fold_right wire_acc 1%nat (labels_of_nibbles ns ++ IP6_ARPA)) <= 255)%N.
    rewrite fold_right_app, wire_base_suffix_ip6_arpa.
    rewrite (fold_right_wire_acc_hexs (labels_of_nibbles ns) Hall1).
    rewrite Hlen_hexs.
    simpl. lia.
  - rewrite Forall_app; split.
    + assert (Hnib : Forall (fun n => n < two4) ns)
        by (apply nibbles_rev_of_bytes_bounds).
      apply Forall_impl with (P := fun s => strlen s = 1%nat).
      * intros s Hs. unfold label_ok. rewrite Hs. lia.
      * subst hexs. now apply labels_of_nibbles_all_len1.
    + repeat constructor; cbn; lia.
Qed.

Lemma additional_contains_A_when_needed :
  forall qt, needs_additional qt = true -> In RT_A (additional_glue qt).
Proof.
  intros [] H; cbn in *; try discriminate; auto.
Qed.

(* =============================================================================
   Section 8b: Bridging Lemma for Bytes Pipeline and an Internal Round-trip
   ============================================================================= *)

Lemma labels_of_nibbles_length :
  forall ns, List.length (labels_of_nibbles ns) = List.length ns.
Proof. intros ns; unfold labels_of_nibbles; now rewrite map_length. Qed.

(* =============================================================================
   Section 8c: AAAA RDATA Codec Inverse Lemmas
   ============================================================================= *)

Theorem decode_encode_AAAA_rdata_normalized :
  forall ip, decode_AAAA_rdata (encode_AAAA_rdata ip) = Some (normalize128 ip).
Proof. intro ip; unfold decode_AAAA_rdata, encode_AAAA_rdata; now apply ipv6_bytes_roundtrip. Qed.

Theorem decode_encode_AAAA_rdata_wf :
  forall ip, wf_ipv6 ip -> decode_AAAA_rdata (encode_AAAA_rdata ip) = Some ip.
Proof. intros ip Hwf; unfold decode_AAAA_rdata, encode_AAAA_rdata; now apply ipv6_bytes_roundtrip_wf. Qed.

(* Converse direction: encode ∘ decode on well-formed byte lists *)

Definition wf_bytes (bs : list byte) : Prop :=
  List.length bs = 16%nat /\ Forall (fun b => b < two8) bs.

Lemma ipv6_to_bytes_to_word32 : forall a b c d,
  ipv6_to_bytes (a, b, c, d) =
  (word32_to_bytes a ++ word32_to_bytes b ++
  word32_to_bytes c ++ word32_to_bytes d)%list.
Proof. intros; reflexivity. Qed.

Lemma app_split_16 : forall {A} (l : list A),
  List.length l = 16%nat ->
  exists a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3,
    l = [a0;a1;a2;a3;b0;b1;b2;b3;c0;c1;c2;c3;d0;d1;d2;d3].
Proof.
  intros A l H.
  destruct l as [|x0 l]; [discriminate|].
  destruct l as [|x1 l]; [discriminate|].
  destruct l as [|x2 l]; [discriminate|].
  destruct l as [|x3 l]; [discriminate|].
  destruct l as [|x4 l]; [discriminate|].
  destruct l as [|x5 l]; [discriminate|].
  destruct l as [|x6 l]; [discriminate|].
  destruct l as [|x7 l]; [discriminate|].
  destruct l as [|x8 l]; [discriminate|].
  destruct l as [|x9 l]; [discriminate|].
  destruct l as [|x10 l]; [discriminate|].
  destruct l as [|x11 l]; [discriminate|].
  destruct l as [|x12 l]; [discriminate|].
  destruct l as [|x13 l]; [discriminate|].
  destruct l as [|x14 l]; [discriminate|].
  destruct l as [|x15 l]; [discriminate|].
  destruct l as [|bad l]; [|discriminate].
  exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15.
  reflexivity.
Qed.

Lemma Forall_16_split : forall (P : byte -> Prop) a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3,
  Forall P [a0;a1;a2;a3;b0;b1;b2;b3;c0;c1;c2;c3;d0;d1;d2;d3] ->
  P a0 /\ P a1 /\ P a2 /\ P a3 /\
  P b0 /\ P b1 /\ P b2 /\ P b3 /\
  P c0 /\ P c1 /\ P c2 /\ P c3 /\
  P d0 /\ P d1 /\ P d2 /\ P d3.
Proof.
  intros P a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 H.
  repeat match goal with
  | H: Forall _ (_ :: _) |- _ => inversion H; clear H; subst
  end.
  repeat split; assumption.
Qed.

Lemma bytes_to_word32_of_word32_to_bytes_normalized : forall w,
  bytes_to_word32 (word32_to_bytes w) = Some (to_word32 w).
Proof.
  intro w.
  apply word32_bytes_roundtrip.
Qed.

Lemma word32_to_bytes_to_word32_exact : forall b0 b1 b2 b3,
  b0 < two8 -> b1 < two8 -> b2 < two8 -> b3 < two8 ->
  word32_to_bytes (to_word32 (b0 * two24 + b1 * two16 + b2 * two8 + b3)) = [b0; b1; b2; b3].
Proof.
  intros.
  apply bytes_word32_roundtrip; assumption.
Qed.

Lemma ipv6_from_bytes_16 : forall a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3,
  Forall (fun b => b < two8) [a0;a1;a2;a3;b0;b1;b2;b3;c0;c1;c2;c3;d0;d1;d2;d3] ->
  ipv6_from_bytes [a0;a1;a2;a3;b0;b1;b2;b3;c0;c1;c2;c3;d0;d1;d2;d3] =
  Some (to_word32 (a0 * two24 + a1 * two16 + a2 * two8 + a3),
        to_word32 (b0 * two24 + b1 * two16 + b2 * two8 + b3),
        to_word32 (c0 * two24 + c1 * two16 + c2 * two8 + c3),
        to_word32 (d0 * two24 + d1 * two16 + d2 * two8 + d3)).
Proof.
  intros.
  apply Forall_16_split in H.
  destruct H as [Ha0 [Ha1 [Ha2 [Ha3 [Hb0 [Hb1 [Hb2 [Hb3 [Hc0 [Hc1 [Hc2 [Hc3 [Hd0 [Hd1 [Hd2 Hd3]]]]]]]]]]]]]]].
  unfold ipv6_from_bytes, bytes_to_word32.
  reflexivity.
Qed.

Theorem encode_decode_AAAA_rdata_exact : forall bs,
  wf_bytes bs ->
  match decode_AAAA_rdata bs with
  | Some ip => encode_AAAA_rdata ip = bs
  | None => False
  end.
Proof.
  intros bs [Hlen Hbound].
  unfold decode_AAAA_rdata, encode_AAAA_rdata.
  destruct (app_split_16 bs Hlen) as [a0 [a1 [a2 [a3 [b0 [b1 [b2 [b3 [c0 [c1 [c2 [c3 [d0 [d1 [d2 [d3 Heq]]]]]]]]]]]]]]]].
  subst bs.
  rewrite ipv6_from_bytes_16 by assumption.
  unfold ipv6_to_bytes.
  repeat rewrite word32_to_bytes_to_word32_exact by
    (apply Forall_16_split in Hbound;
     repeat match goal with
     | H: _ /\ _ |- _ => destruct H
     end; assumption).
  reflexivity.
Qed.

Corollary encode_decode_AAAA_rdata : forall bs ip,
  wf_bytes bs ->
  decode_AAAA_rdata bs = Some ip ->
  encode_AAAA_rdata ip = bs.
Proof.
  intros bs ip Hwf Hdec.
  generalize (encode_decode_AAAA_rdata_exact bs Hwf).
  rewrite Hdec.
  intro H; exact H.
Qed.

(* === AAAA RDATA Codec Canonicalization Theorems ===

   These theorems establish that AAAA RDATA encoding and decoding form
   a bijection on well-formed byte sequences (16 octets, each < 256).

   RFC 3596 §2.2 specifies AAAA RDATA as exactly 16 octets in network order.
   Wire-format parsers must validate octet ranges before interpretation. *)

Theorem decode_encode_AAAA_canonical : forall bs ip,
  wf_bytes bs ->
  decode_AAAA_rdata bs = Some ip ->
  encode_AAAA_rdata ip = bs.
Proof.
  intros bs ip Hwf Hdec.
  apply encode_decode_AAAA_rdata; assumption.
Qed.

(* Successful decoding of well-formed bytes produces well-formed IPv6 addresses.
   All four 32-bit components satisfy the bound x < 2^32. *)
Theorem decode_AAAA_produces_wf : forall bs ip,
  wf_bytes bs ->
  decode_AAAA_rdata bs = Some ip ->
  wf_ipv6 ip.
Proof.
  intros bs ip [Hlen Hbounds] Hdec.
  unfold decode_AAAA_rdata in Hdec.
  apply ipv6_from_bytes_some_bounds with (bytes := bs).
  - exact Hdec.
  - exact Hbounds.
Qed.

(* AAAA codec stability: encode(decode(bs)) = bs for well-formed byte sequences.
   This property ensures that wire-format parsers produce canonical output. *)
Theorem AAAA_codec_stable : forall bs,
  wf_bytes bs ->
  match decode_AAAA_rdata bs with
  | Some ip => encode_AAAA_rdata ip = bs
  | None => True
  end.
Proof.
  intros bs Hwf.
  destruct (decode_AAAA_rdata bs) eqn:E; [|trivial].
  apply decode_encode_AAAA_canonical; assumption.
Qed.

(* =============================================================================
   Section 9: Computational Examples
   ============================================================================= *)

Definition example_loopback : word128 := (0, 0, 0, 1).
Definition example_doc : word128 := (0x20010db8, 0, 0, 1).
Definition example_domain : list string := ["www"; "example"; "com"].

(* AAAA record creation *)

Definition example_aaaa : AAAARecord :=
  create_aaaa_record example_domain example_doc 3600.

Example aaaa_well_formed :
  example_aaaa.(aaaa_type) = AAAA_TYPE /\
  example_aaaa.(aaaa_class) = IN_CLASS /\
  example_aaaa.(aaaa_rdlength) = 16.
Proof. split; [|split]; reflexivity. Qed.

(* AAAA RDATA encoding *)

Definition example_rdata : list byte := encode_AAAA_rdata example_doc.

Example rdata_length : List.length example_rdata = 16%nat.
Proof. reflexivity. Qed.

Example rdata_first_word :
  match example_rdata with
  | b0::b1::b2::b3::_ => (b0, b1, b2, b3) = (32, 1, 13, 184)
  | _ => False
  end.
Proof. reflexivity. Qed.

Example rdata_last_word :
  match List.rev example_rdata with
  | b3::b2::b1::b0::_ => (b0, b1, b2, b3) = (0, 0, 0, 1)
  | _ => False
  end.
Proof. reflexivity. Qed.

(* AAAA RDATA decoding *)

Definition example_decoded : option word128 := decode_AAAA_rdata example_rdata.

Example decode_succeeds : example_decoded = Some (normalize128 example_doc).
Proof. reflexivity. Qed.

Example rdata_roundtrip :
  decode_AAAA_rdata (encode_AAAA_rdata example_doc) = Some (normalize128 example_doc).
Proof. reflexivity. Qed.

(* IPv6 reverse DNS *)

Definition example_reverse_name : list string := ipv6_to_reverse example_loopback.

Example reverse_name_length : List.length example_reverse_name = 34%nat.
Proof. reflexivity. Qed.

Example reverse_name_suffix :
  match List.rev example_reverse_name with
  | a :: i :: _ => eq_label_ci a "arpa" = true /\ eq_label_ci i "ip6" = true
  | _ => False
  end.
Proof. split; reflexivity. Qed.

Example reverse_name_first :
  match example_reverse_name with
  | first :: _ => eq_label_ci first "1" = true
  | _ => False
  end.
Proof. reflexivity. Qed.

Definition example_reverse_decoded : option word128 :=
  reverse_to_ipv6 example_reverse_name.

Example reverse_decode_succeeds :
  example_reverse_decoded = Some (normalize128 example_loopback).
Proof. reflexivity. Qed.

Example reverse_roundtrip :
  reverse_to_ipv6 (ipv6_to_reverse example_loopback) = Some (normalize128 example_loopback).
Proof. reflexivity. Qed.

(* Case-insensitive reverse DNS *)

Definition example_reverse_upper : list string :=
  let nibbles := match List.rev example_reverse_name with
                 | a :: i :: rest => List.rev rest
                 | _ => []
                 end in
  nibbles ++ ["IP6"; "ARPA"].

Example reverse_case_insensitive :
  reverse_to_ipv6 example_reverse_upper = Some (normalize128 example_loopback).
Proof.
  unfold example_reverse_upper, example_reverse_name, example_loopback.
  unfold ipv6_to_reverse, reverse_to_ipv6, ipv6_to_bytes.
  simpl word32_to_bytes. simpl app.
  unfold labels_of_nibbles, nibbles_rev_of_bytes.
  simpl flat_map. simpl rev. simpl app.
  unfold IP6_ARPA, strip_ip6_arpa.
  simpl rev.
  unfold eq_label_ci, to_lower.
  simpl to_lower_ascii. simpl String.eqb. simpl andb. simpl rev.
  unfold nibbles_of_labels. simpl map.
  unfold label_to_nibble, ascii_to_nibble. simpl.
  unfold sequence. simpl.
  unfold bytes_from_nibbles_rev. simpl.
  unfold ipv6_from_bytes, bytes_to_word32, to_word32. simpl.
  unfold normalize128. reflexivity.
Qed.

(* Additional-section processing *)

Example ns_needs_glue : needs_additional RT_NS = true.
Proof. reflexivity. Qed.

Example ns_glue_includes_aaaa : In RT_AAAA (additional_glue RT_NS).
Proof. simpl. auto. Qed.

Example ns_glue_includes_a : In RT_A (additional_glue RT_NS).
Proof. simpl. auto. Qed.

(* Dual-stack strategy *)

Definition example_dual_stack : DualStackConfig :=
  {| ds_prefer_ipv6 := true; ds_ipv6_only := false; ds_ipv4_only := false |}.

Example dual_stack_strategy : determine_strategy example_dual_stack = QS_AAAA_THEN_A.
Proof. reflexivity. Qed.

Definition example_ipv6_only : DualStackConfig :=
  {| ds_prefer_ipv6 := true; ds_ipv6_only := true; ds_ipv4_only := false |}.

Example ipv6_only_strategy : determine_strategy example_ipv6_only = QS_AAAA_ONLY.
Proof. reflexivity. Qed.

(* Transport selection *)

Definition example_transport : IPv6Transport :=
  {| t6_has_ipv6 := true; t6_has_ipv4 := true |}.

Example select_ipv6_when_available :
  select_transport example_transport true false = Some UseIPv6.
Proof. reflexivity. Qed.

Example fallback_to_ipv4 :
  select_transport example_transport false true = Some UseIPv4.
Proof. reflexivity. Qed.

(* =============================================================================
   Section 10: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool   => "bool" [ "true" "false" ].
Extract Inductive list   => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" [ "Some" "None" ].

From Coq Require Import ExtrOcamlZBigInt ExtrOcamlString.
Extraction Language OCaml.

Extraction "dns_ipv6.ml"
  create_aaaa_record
  ipv6_to_reverse
  reverse_to_ipv6
  determine_strategy
  select_transport
  additional_glue
  (* RDATA codec *)
  encode_AAAA_rdata
  decode_AAAA_rdata.
