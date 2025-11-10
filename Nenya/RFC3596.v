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

Definition byte    := N.  (* 0..255 *)
Definition word16  := N.  (* 0..65535 *)
Definition word32  := N.  (* modulo 2^32 via [to_word32] *)
Definition word128 := (word32 * word32 * word32 * word32)%type.

(* numeric helpers *)
Definition two4  : N := 16.
Definition two8  : N := 256.
Definition two16 : N := 65536.
Definition two24 : N := 16777216.        (* 2^24 *)
Definition two32 : N := 4294967296.      (* 2^32 *)

Definition to_byte   (x:N) : byte   := x mod two8.
Definition to_word16 (x:N) : word16 := x mod two16.
Definition to_word32 (x:N) : word32 := x mod two32.

Lemma to_byte_small : forall x, x < two8 -> to_byte x = x.
Proof. intros x H; unfold to_byte; apply N.mod_small; exact H. Qed.

(* IPv6 DNS constants (RFC 3596) *)
Definition AAAA_TYPE : word16 := 28.        (* §2.1 *)
Definition PTR_TYPE  : word16 := 12.        (* RFC 1035 *)
Definition IN_CLASS  : word16 := 1.

Definition IP6_ARPA : list string := ["ip6"; "arpa"].
Definition IP6_INT  : list string := ["ip6"; "int"].  (* historical; not used *)

(* strings *)
Fixpoint strlen (s:string) : nat :=
  match s with
  | EmptyString => 0%nat
  | String _ tl => S (strlen tl)
  end.

Definition domain_name_wire_len (labs:list string) : N :=
  (* sum (1 + |label|) + 1 for root zero-length label; RFC 1035 *)
  N.of_nat (List.fold_right (fun s acc => S (strlen s) + acc)%nat 1%nat labs).

Definition domain_name_length (labs:list string) : word16 :=
  to_word16 (domain_name_wire_len labs).

(* =============================================================================
   Section 2: AAAA Resource Record (RFC 3596 Section 2.1/2.2)
   ============================================================================= *)

(* 32-bit big-endian (network order) packing/unpacking *)
Definition word32_to_bytes (w:word32) : list byte :=
  [ (w / two24) mod two8;
    (w / two16) mod two8;
    (w / two8 ) mod two8;
    w mod two8 ].

Definition bytes_to_word32 (bs:list byte) : option word32 :=
  match bs with
  | [b0;b1;b2;b3] =>
      Some (to_word32 (b0 * two24 + b1 * two16 + b2 * two8 + b3))
  | _ => None
  end.

(* IPv6 address representation *)
Definition ipv6_to_bytes (addr : word128) : list byte :=
  let '(a,b,c,d) := addr in
  word32_to_bytes a ++ word32_to_bytes b ++
  word32_to_bytes c ++ word32_to_bytes d.

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

(* AAAA RR as in RFC 3596 *)
Record AAAARecord := {
  aaaa_name     : list string;
  aaaa_type     : word16;         (* must be 28 *)
  aaaa_class    : word16;         (* must be IN (1) *)
  aaaa_ttl      : word32;
  aaaa_rdlength : word16;         (* must be 16 *)
  aaaa_address  : word128         (* 16 octets, network order *)
}.

(* Smart constructor enforces spec-mandated fields (§2.1/2.2) *)
Definition create_aaaa_record (name : list string) (addr : word128) (ttl : word32)
  : AAAARecord :=
  {| aaaa_name := name;
     aaaa_type := AAAA_TYPE;
     aaaa_class := IN_CLASS;
     aaaa_ttl := ttl;
     aaaa_rdlength := 16;
     aaaa_address := addr |}.

Lemma aaaa_fixed_size_create : forall name addr ttl,
  (create_aaaa_record name addr ttl).(aaaa_rdlength) = 16.
Proof. reflexivity. Qed.

(* Optional well-formedness predicate useful for generic AAAA RRs *)
Record AAAA_wf (r:AAAARecord) : Prop := {
  WF_type  : r.(aaaa_type) = AAAA_TYPE;
  WF_class : r.(aaaa_class) = IN_CLASS;
  WF_len   : r.(aaaa_rdlength) = 16
}.

Theorem aaaa_fixed_size_wf : forall r, AAAA_wf r -> r.(aaaa_rdlength) = 16.
Proof. intros r H; exact (WF_len _ H). Qed.

(* =============================================================================
   Section 2b: AAAA RDATA Codec (RDATA = 16-octet IPv6 address)
   ============================================================================= *)

Definition encode_AAAA_rdata (addr:word128) : list byte :=
  ipv6_to_bytes addr.

Definition decode_AAAA_rdata (bs:list byte) : option word128 :=
  ipv6_from_bytes bs.

(* We will prove inverse properties in Section 8c after developing shared lemmas. *)

(* =============================================================================
   Section 3: IPv6 Reverse Mapping (RFC 3596 Section 2.5)
   ============================================================================= *)

(* nibbles *)
Definition hi_nib (b:byte) : N := (b / two4) mod two4.
Definition lo_nib (b:byte) : N := b mod two4.

Lemma hi_nib_small : forall b, b < two8 -> (b / two4) < two4.
Proof.
  intros b Hb.
  unfold two8, two4 in *.
  apply N.Div0.div_lt_upper_bound; lia.
Qed.

Lemma byte_decompose : forall b, b < two8 -> two4 * (b / two4) + (b mod two4) = b.
Proof.
  intros b Hb.
  rewrite <- (N.div_mod b two4) at 1.
  - reflexivity.
  - unfold two4; lia.
Qed.

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

(* hex digit <-> one-char label *)
Definition singleton (c:ascii) : string := String c EmptyString.

Definition nibble_label_of (n:N) : string :=
  match N.to_nat n with
  | 0%nat => "0"%string | 1%nat => "1"%string | 2%nat => "2"%string | 3%nat => "3"%string
  | 4%nat => "4"%string | 5%nat => "5"%string | 6%nat => "6"%string | 7%nat => "7"%string
  | 8%nat => "8"%string | 9%nat => "9"%string
  | 10%nat => "a"%string | 11%nat => "b"%string | 12%nat => "c"%string
  | 13%nat => "d"%string | 14%nat => "e"%string | 15%nat => "f"%string
  | _ => "0"%string (* unreachable for n<16 *)
  end.

Definition ascii_to_nibble (c:ascii) : option N :=
  let n := nat_of_ascii c in
  if (48 <=? n)%nat && (n <=? 57)%nat then Some (N.of_nat (n - 48)%nat) else
  if (97 <=? n)%nat && (n <=? 102)%nat then Some (N.of_nat (n - 87)%nat) else
  if (65 <=? n)%nat && (n <=? 70)%nat then Some (N.of_nat (n - 55)%nat) else
  None.

Definition label_to_nibble (s:string) : option N :=
  match s with
  | String c EmptyString => ascii_to_nibble c
  | _ => None
  end.

Lemma nibble_to_nat_bound : forall n,
  n < two4 -> (N.to_nat n < 16)%nat.
Proof.
  intros n H. unfold two4 in H.
  repeat match goal with
  | H: N.succ _ < _ |- _ => apply N.lt_succ_r in H
  end.
  destruct n; cbn; lia.
Qed.

Lemma label_of_nibble_inverse : forall n,
  n < two4 -> label_to_nibble (nibble_label_of n) = Some n.
Proof.
  intros n Hlt.
  unfold two4 in Hlt.
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

(* option list utilities *)
Fixpoint sequence {A} (xs:list (option A)) : option (list A) :=
  match xs with
  | [] => Some []
  | Some x :: tl => option_map (fun r => x::r) (sequence tl)
  | None :: _ => None
  end.

(* Produce the 32 nibbles in the ip6.arpa order:
   low-order nibble of last byte first, then its high nibble, then previous byte, ... *)
Fixpoint nibbles_rev_of_bytes (bs:list byte) : list N :=
  match bs with
  | [] => []
  | b::tl => nibbles_rev_of_bytes tl ++ [lo_nib b; hi_nib b]
  end.

Definition labels_of_nibbles (ns:list N) : list string :=
  map nibble_label_of ns.

Definition nibbles_of_labels (ls:list string) : option (list N) :=
  sequence (map label_to_nibble ls).

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

(* bytes <-> nibbles (in the ip6.arpa ordering) *)
Fixpoint bytes_from_nibbles_rev (ns:list N) : option (list byte) :=
  match ns with
  | [] => Some []
  | lo::hi::tl =>
      option_map (fun r => to_byte (two4*hi + lo) :: r) (bytes_from_nibbles_rev tl)
  | _ => None
  end.

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

Lemma bytes_from_nibbles_rev_of_bytes :
  forall bs,
    Forall (fun b => b < two8) bs ->
    bytes_from_nibbles_rev (nibbles_rev_of_bytes bs) = Some (rev bs).
Proof.
  induction bs as [|b bs' IH]; intro Hall; [reflexivity|].
  inversion Hall as [|? ? Hb Hbs']; subst.
  simpl nibbles_rev_of_bytes.
  specialize (IH Hbs').
  assert (H_app: bytes_from_nibbles_rev (nibbles_rev_of_bytes bs' ++ [lo_nib b; hi_nib b])%list =
                 Some (rev bs' ++ [to_byte (two4 * hi_nib b + lo_nib b)])%list).
  { apply bytes_from_nibbles_rev_app. exact IH. }
  rewrite H_app. rewrite nibbles_reconstruct_byte by exact Hb.
  simpl. reflexivity.
Qed.

(* Suffix handling *)
Definition strip_ip6_arpa (labs:list string) : option (list string) :=
  match rev labs with
  | "arpa" :: "ip6" :: rest_rev => Some (rev rest_rev)
  | _ => None
  end.

(* Convert IPv6 address to reverse DNS name (RFC 3596 §2.5) *)
Definition ipv6_to_reverse (addr : word128) : list string :=
  let bytes := ipv6_to_bytes addr in
  labels_of_nibbles (nibbles_rev_of_bytes bytes) ++ IP6_ARPA.

(* Decode reverse name back to IPv6 *)
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

(* helper: all bytes from word32_to_bytes are < 256 *)
Lemma word32_to_bytes_bounds : forall w,
  Forall (fun b => b < two8) (word32_to_bytes w).
Proof.
  intro w; unfold word32_to_bytes.
  repeat constructor; apply N.mod_lt; unfold two8; lia.
Qed.

Lemma ipv6_bytes_bounds : forall a b c d,
  Forall (fun x => x < two8) (ipv6_to_bytes (a,b,c,d)).
Proof.
  intros; unfold ipv6_to_bytes.
  repeat rewrite Forall_app; repeat split; apply word32_to_bytes_bounds.
Qed.

Lemma word32_byte0_lt : forall w, w / two24 mod two8 < two8.
Proof. intros; apply N.mod_lt; unfold two8; lia. Qed.

Lemma word32_byte1_lt : forall w, w / two16 mod two8 < two8.
Proof. intros; apply N.mod_lt; unfold two8; lia. Qed.

Lemma word32_byte2_lt : forall w, w / two8 mod two8 < two8.
Proof. intros; apply N.mod_lt; unfold two8; lia. Qed.

Lemma word32_byte3_lt : forall w, w mod two8 < two8.
Proof. intros; apply N.mod_lt; unfold two8; lia. Qed.

Lemma mod_small_iff : forall a b, b <> 0 -> a < b -> a mod b = a.
Proof. intros. apply N.mod_small. lia. Qed.

Lemma mod_of_mod_small : forall a b, b <> 0 -> a mod b < b.
Proof. intros. apply N.mod_lt. lia. Qed.

Lemma add_mod_cancel_mult : forall a k m, m <> 0 -> (a + k * m) mod m = a mod m.
Proof.
  intros. apply N.Div0.mod_add; lia.
Qed.

Lemma add_mod_cancel_mult_l : forall a k m, m <> 0 -> (k * m + a) mod m = a mod m.
Proof.
  intros. replace (k * m + a) with (a + k * m) by lia.
  apply add_mod_cancel_mult. lia.
Qed.

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

Lemma mod256_of_mod65536 : forall w,
  (w mod 65536) mod 256 = w mod 256.
Proof.
  intros. replace 65536 with (256 * 256) by lia.
  apply mod_mod_cancel; lia.
Qed.

Lemma div_add_cancel : forall a k m, m <> 0 -> (k * m + a) / m = k + a / m.
Proof.
  intros. replace (k * m + a) with (a + k * m) by lia.
  rewrite N.div_add by lia. lia.
Qed.

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

Lemma div256_of_mod65536 : forall w,
  (w mod 65536) / 256 = w / 256 mod 256.
Proof.
  intros. replace 65536 with (256 * 256) by lia.
  apply div_mod_swap; lia.
Qed.

Lemma mod65536_of_mod16777216 : forall w,
  (w mod 16777216) mod 65536 = w mod 65536.
Proof.
  intros. replace 16777216 with (256 * 65536) by lia.
  apply mod_mod_cancel; lia.
Qed.

Lemma div65536_of_mod16777216 : forall w,
  (w mod 16777216) / 65536 = w / 65536 mod 256.
Proof.
  intros. replace 16777216 with (256 * 65536) by lia.
  apply div_mod_swap; lia.
Qed.

Lemma div16777216_lt256 : forall w, w < 4294967296 -> w / 16777216 < 256.
Proof. intros. apply N.Div0.div_lt_upper_bound; lia. Qed.

Lemma div_mod_compat_256 : forall w d,
  d <> 0 -> 256 <> 0 ->
  w / d mod 256 = (w mod (256 * d)) / d mod 256.
Proof.
  intros w d Hd H256.
  rewrite div_mod_swap by lia.
  rewrite N.Div0.mod_mod by lia.
  reflexivity.
Qed.

Lemma byte_reconstruction_step1 : forall w,
  w < 4294967296 ->
  w = (w / 16777216) * 16777216 + w mod 16777216.
Proof.
  intros.
  rewrite N.mul_comm.
  apply N.div_mod. lia.
Qed.

Lemma byte_reconstruction_step2 : forall w,
  w mod 16777216 = (w / 65536 mod 256) * 65536 + w mod 65536.
Proof.
  intros.
  rewrite (N.div_mod (w mod 16777216) 65536) at 1 by lia.
  rewrite div65536_of_mod16777216, mod65536_of_mod16777216.
  rewrite N.mul_comm.
  reflexivity.
Qed.

Lemma byte_reconstruction_step3 : forall w,
  w mod 65536 = (w / 256 mod 256) * 256 + w mod 256.
Proof.
  intros.
  rewrite (N.div_mod (w mod 65536) 256) at 1 by lia.
  rewrite div256_of_mod65536, mod256_of_mod65536.
  rewrite N.mul_comm.
  reflexivity.
Qed.

Lemma mod_256_of_mod_2_32 : forall w,
  w mod 256 = (w mod 4294967296) mod 256.
Proof.
  intros. replace 4294967296 with (16777216 * 256) by lia.
  symmetry. apply mod_mod_cancel; lia.
Qed.

Lemma div_256_mod_256_of_mod_2_32 : forall w,
  w / 256 mod 256 = (w mod 4294967296) / 256 mod 256.
Proof.
  intros.
  replace 4294967296 with (16777216 * 256) by lia.
  rewrite div_mod_swap by lia.
  replace 16777216 with (65536 * 256) by lia.
  symmetry. apply mod_mod_cancel; lia.
Qed.

Lemma div_65536_mod_256_of_mod_2_32 : forall w,
  w / 65536 mod 256 = (w mod 4294967296) / 65536 mod 256.
Proof.
  intros.
  replace 4294967296 with (65536 * 65536) by lia.
  rewrite div_mod_swap by lia.
  replace 65536 with (256 * 256) by lia.
  symmetry. apply mod_mod_cancel; lia.
Qed.

Lemma mod_mod_same : forall a m, m <> 0 -> (a mod m) mod m = a mod m.
Proof.
  intros. apply N.mod_small. apply N.mod_lt. assumption.
Qed.

Lemma div_16777216_mod_256_of_mod_2_32 : forall w,
  w / 16777216 mod 256 = (w mod 4294967296) / 16777216 mod 256.
Proof.
  intros. replace 4294967296 with (256 * 16777216) by lia.
  rewrite div_mod_swap by lia.
  symmetry. apply mod_mod_same. lia.
Qed.

Lemma byte0_eq : forall w, w mod 256 = (w mod 4294967296) mod 256.
Proof. intros. apply mod_256_of_mod_2_32. Qed.

Lemma byte1_eq : forall w, w / 256 mod 256 = (w mod 4294967296) / 256 mod 256.
Proof. intros. apply div_256_mod_256_of_mod_2_32. Qed.

Lemma byte2_eq : forall w, w / 65536 mod 256 = (w mod 4294967296) / 65536 mod 256.
Proof. intros. apply div_65536_mod_256_of_mod_2_32. Qed.

Lemma byte3_eq : forall w, w / 16777216 mod 256 = (w mod 4294967296) / 16777216 mod 256.
Proof. intros. apply div_16777216_mod_256_of_mod_2_32. Qed.

Lemma byte3_normalized : forall w, w < 4294967296 -> w / 16777216 < 256.
Proof. intros. apply div16777216_lt256. assumption. Qed.

Lemma byte3_mod_small : forall w, w < 4294967296 -> w / 16777216 mod 256 = w / 16777216.
Proof. intros. apply N.mod_small. apply byte3_normalized. assumption. Qed.

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

Lemma word32_reconstruction : forall w,
  (w / two24 mod two8) * two24 +
  (w / two16 mod two8) * two16 +
  (w / two8 mod two8) * two8 +
  (w mod two8) = w mod two32.
Proof.
  intro w. unfold two24, two16, two8, two32.
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

Lemma to_word32_of_bytes_eq : forall w,
  to_word32 ((w / two24 mod two8) * two24 +
             (w / two16 mod two8) * two16 +
             (w / two8 mod two8) * two8 +
             (w mod two8)) = to_word32 w.
Proof.
  intro w. unfold to_word32.
  rewrite word32_reconstruction.
  apply N.Div0.mod_mod; unfold two32; lia.
Qed.

Lemma word32_bytes_roundtrip : forall w,
  bytes_to_word32 (word32_to_bytes w) = Some (to_word32 w).
Proof.
  intro w. unfold word32_to_bytes, bytes_to_word32, to_word32.
  repeat rewrite N.mod_small by (apply word32_byte0_lt || apply word32_byte1_lt ||
                                  apply word32_byte2_lt || apply word32_byte3_lt).
  f_equal. rewrite word32_reconstruction. assert (H: two32 <> 0) by (unfold two32; lia).
  rewrite N.Div0.mod_mod by exact H. reflexivity.
Qed.

(* Normalization on 128-bit tuples (reduces components modulo 2^32) *)
Definition normalize128 (ip:word128) : word128 :=
  let '(a,b,c,d) := ip in (to_word32 a, to_word32 b, to_word32 c, to_word32 d).

Lemma strip_ip6_arpa_app_hex :
  forall hexs, strip_ip6_arpa (hexs ++ IP6_ARPA) = Some hexs.
Proof.
  intro hexs; unfold strip_ip6_arpa.
  rewrite rev_app_distr; cbn. now rewrite rev_involutive.
Qed.

Lemma nibbles_rev_of_bytes_length : forall bs,
  List.length (nibbles_rev_of_bytes bs) = (2 * List.length bs)%nat.
Proof.
  induction bs as [|b tl IH]; simpl; [reflexivity|].
  rewrite app_length, IH. simpl. lia.
Qed.

Lemma word32_to_bytes_length : forall w,
  List.length (word32_to_bytes w) = 4%nat.
Proof. intros; reflexivity. Qed.

Lemma ipv6_to_bytes_length : forall a b c d,
  List.length (ipv6_to_bytes (a,b,c,d)) = 16%nat.
Proof.
  intros; unfold ipv6_to_bytes.
  repeat rewrite app_length.
  now rewrite !word32_to_bytes_length.
Qed.

Lemma nibbles_rev_of_bytes_bounds :
  forall bs, Forall (fun n => n < two4) (nibbles_rev_of_bytes bs).
Proof.
  induction bs as [|b tl IH]; simpl; [constructor|].
  rewrite Forall_app; split; [assumption|].
  repeat constructor; apply N.mod_lt; unfold two4; lia.
Qed.

(* Round-trip property (left-inverse) up to 32-bit normalization *)
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

(* If each component is already within 32-bit bounds, we get exact bijection *)
Definition wf_ipv6 (ip:word128) : Prop :=
  let '(a,b,c,d) := ip in a < two32 /\ b < two32 /\ c < two32 /\ d < two32.

Lemma to_word32_id_if_lt : forall x, x < two32 -> to_word32 x = x.
Proof. intros x H; unfold to_word32; apply N.mod_small; exact H. Qed.

Theorem reverse_bijective :
  forall ip, wf_ipv6 ip -> reverse_to_ipv6 (ipv6_to_reverse ip) = Some ip.
Proof.
  intros [[[a b] c] d] [Ha [Hb [Hc Hd]]].
  rewrite reverse_roundtrip_normalized.
  unfold normalize128.
  now rewrite !to_word32_id_if_lt.
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

Definition select_transport (transport : IPv6Transport) 
                            (has_aaaa has_a : bool) : option bool :=
  if andb has_aaaa transport.(t6_has_ipv6) then Some true
  else if andb has_a transport.(t6_has_ipv4) then Some false
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
  unfold two4 in Hlt.
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

(* The reverse pipeline specialized to an IPv6 address reduces to raw bytes. *)
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

(* Consequence: raw byte round-trip for IPv6 addresses (no labels) *)
Theorem ipv6_bytes_roundtrip :
  forall ip, ipv6_from_bytes (ipv6_to_bytes ip) = Some (normalize128 ip).
Proof.
  intro ip.
  pose proof (reverse_roundtrip_normalized ip) as H.
  rewrite (reverse_bytes_pipeline_equiv ip) in H.
  exact H.
Qed.

(* Under well-formed 32-bit components, the round-trip is exact. *)
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

(* =============================================================================
   Section 8c: AAAA RDATA Codec Inverse Lemmas
   ============================================================================= *)

Theorem decode_encode_AAAA_rdata_normalized :
  forall ip, decode_AAAA_rdata (encode_AAAA_rdata ip) = Some (normalize128 ip).
Proof. intro ip; unfold decode_AAAA_rdata, encode_AAAA_rdata; now apply ipv6_bytes_roundtrip. Qed.

Theorem decode_encode_AAAA_rdata_wf :
  forall ip, wf_ipv6 ip -> decode_AAAA_rdata (encode_AAAA_rdata ip) = Some ip.
Proof. intros ip Hwf; unfold decode_AAAA_rdata, encode_AAAA_rdata; now apply ipv6_bytes_roundtrip_wf. Qed.

(* Note: The converse direction (encode ∘ decode) yields a canonicalization of
   RDATA bytes. If the input bytes are all < 256 and exactly 16 octets long, the
   canonical bytes coincide with the input; formalizing that requires a few
   base-256 arithmetic lemmas. The RFC only specifies the abstract 128-bit
   value, so the essential inverse properties above (normalized and wf) suffice
   for spec coverage of RDATA. *)

(* =============================================================================
   Section 9: Extraction
   ============================================================================= *)

Require Extraction.
Extract Inductive bool   => "bool" [ "true" "false" ].
Extract Inductive list   => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" [ "Some" "None" ].

(* Optional OCaml tuning (uncomment if targeting OCaml with Zarith & native strings)
From Coq Require Import ExtrOcamlZBigInt ExtrOcamlString.
Extraction Language OCaml.
*)

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
