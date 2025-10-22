
type unit0 =
| Tt

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| _::l' -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

type comparison =
| Eq
| Lt
| Gt

type sumbool =
| Left
| Right

(** val add : nat -> nat -> nat **)

let rec add n0 m =
  match n0 with
  | O -> m
  | S p -> S (add p m)

(** val bool_dec : bool -> bool -> sumbool **)

let bool_dec b1 b2 =
  if b1 then if b2 then Left else Right else if b2 then Right else Left

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x::l' -> app (rev l') (x::[])

(** val list_eq_dec :
    ('a1 -> 'a1 -> sumbool) -> 'a1 list -> 'a1 list -> sumbool **)

let rec list_eq_dec eq_dec0 l l' =
  match l with
  | [] -> (match l' with
           | [] -> Left
           | _::_ -> Right)
  | y::l0 ->
    (match l' with
     | [] -> Right
     | a::l1 ->
       (match eq_dec0 y a with
        | Left -> list_eq_dec eq_dec0 l0 l1
        | Right -> Right))

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a::t -> (f a)::(map f t)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b::t -> fold_left f t (f a0 b)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x::l0 -> if f x then x::(filter f l0) else filter f l0

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val pred_N : positive -> n **)

  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> false)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> false)
    | XH -> (match q with
             | XH -> true
             | _ -> false)

  (** val coq_Nsucc_double : n -> n **)

  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val coq_Ndouble : n -> n **)

  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val coq_lor : positive -> positive -> positive **)

  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH -> (match q with
             | XO q0 -> XI q0
             | _ -> q)

  (** val coq_land : positive -> positive -> n **)

  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH -> (match q with
             | XO _ -> N0
             | _ -> Npos XH)

  (** val shiftl : positive -> n -> positive **)

  let shiftl p = function
  | N0 -> p
  | Npos n1 -> iter (fun x -> XO x) p n1

  (** val testbit : positive -> n -> bool **)

  let rec testbit p n0 =
    match p with
    | XI p0 -> (match n0 with
                | N0 -> true
                | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 -> (match n0 with
                | N0 -> false
                | Npos n1 -> testbit p0 (pred_N n1))
    | XH -> (match n0 with
             | N0 -> true
             | Npos _ -> false)

  (** val eq_dec : positive -> positive -> sumbool **)

  let rec eq_dec p x0 =
    match p with
    | XI p0 -> (match x0 with
                | XI p1 -> eq_dec p0 p1
                | _ -> Right)
    | XO p0 -> (match x0 with
                | XO p1 -> eq_dec p0 p1
                | _ -> Right)
    | XH -> (match x0 with
             | XH -> Left
             | _ -> Right)
 end

module N =
 struct
  (** val add : n -> n -> n **)

  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Coq_Pos.add p q))

  (** val sub : n -> n -> n **)

  let sub n0 m =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n0
       | Npos m' ->
         (match Coq_Pos.sub_mask n' m' with
          | Coq_Pos.IsPos p -> Npos p
          | _ -> N0))

  (** val mul : n -> n -> n **)

  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Npos (Coq_Pos.mul p q))

  (** val compare : n -> n -> comparison **)

  let compare n0 m =
    match n0 with
    | N0 -> (match m with
             | N0 -> Eq
             | Npos _ -> Lt)
    | Npos n' -> (match m with
                  | N0 -> Gt
                  | Npos m' -> Coq_Pos.compare n' m')

  (** val eqb : n -> n -> bool **)

  let eqb n0 m =
    match n0 with
    | N0 -> (match m with
             | N0 -> true
             | Npos _ -> false)
    | Npos p -> (match m with
                 | N0 -> false
                 | Npos q -> Coq_Pos.eqb p q)

  (** val leb : n -> n -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : n -> n -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val div2 : n -> n **)

  let div2 = function
  | N0 -> N0
  | Npos p0 -> (match p0 with
                | XI p -> Npos p
                | XO p -> Npos p
                | XH -> N0)

  (** val coq_lor : n -> n -> n **)

  let coq_lor n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Coq_Pos.coq_lor p q))

  (** val coq_land : n -> n -> n **)

  let coq_land n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Coq_Pos.coq_land p q)

  (** val shiftl : n -> n -> n **)

  let shiftl a n0 =
    match a with
    | N0 -> N0
    | Npos a0 -> Npos (Coq_Pos.shiftl a0 n0)

  (** val shiftr : n -> n -> n **)

  let shiftr a = function
  | N0 -> a
  | Npos p -> Coq_Pos.iter div2 a p

  (** val testbit : n -> n -> bool **)

  let testbit a n0 =
    match a with
    | N0 -> false
    | Npos p -> Coq_Pos.testbit p n0

  (** val eq_dec : n -> n -> sumbool **)

  let eq_dec n0 m =
    match n0 with
    | N0 -> (match m with
             | N0 -> Left
             | Npos _ -> Right)
    | Npos p -> (match m with
                 | N0 -> Right
                 | Npos p0 -> Coq_Pos.eq_dec p p0)
 end

type byte = n

type word16 = n

(** val aRP_HRD_ETHERNET : word16 **)

let aRP_HRD_ETHERNET =
  Npos XH

(** val aRP_PRO_IP : word16 **)

let aRP_PRO_IP =
  Npos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO XH)))))))))))

(** val aRP_OP_REQUEST : word16 **)

let aRP_OP_REQUEST =
  Npos XH

(** val aRP_OP_REPLY : word16 **)

let aRP_OP_REPLY =
  Npos (XO XH)

(** val rARP_OP_REQUEST : word16 **)

let rARP_OP_REQUEST =
  Npos (XI XH)

(** val rARP_OP_REPLY : word16 **)

let rARP_OP_REPLY =
  Npos (XO (XO XH))

(** val eTHERNET_ADDR_LEN : byte **)

let eTHERNET_ADDR_LEN =
  Npos (XO (XI XH))

(** val iPV4_ADDR_LEN : byte **)

let iPV4_ADDR_LEN =
  Npos (XO (XO XH))

(** val is_valid_opcode : word16 -> bool **)

let is_valid_opcode op =
  if if if N.eqb op aRP_OP_REQUEST then true else N.eqb op aRP_OP_REPLY
     then true
     else N.eqb op rARP_OP_REQUEST
  then true
  else N.eqb op rARP_OP_REPLY

(** val is_valid_arp_opcode : word16 -> bool **)

let is_valid_arp_opcode op =
  if N.eqb op aRP_OP_REQUEST then true else N.eqb op aRP_OP_REPLY

type mACAddress =
  byte list
  (* singleton inductive, whose constructor was Build_MACAddress *)

type iPv4Address = { ipv4_a : byte; ipv4_b : byte; ipv4_c : byte;
                     ipv4_d : byte }

(** val mAC_ZERO : mACAddress **)

let mAC_ZERO =
  N0::(N0::(N0::(N0::(N0::(N0::[])))))

(** val is_broadcast_mac : mACAddress -> bool **)

let is_broadcast_mac = function
| [] -> false
| b::l ->
  (match b with
   | N0 -> false
   | Npos p ->
     (match p with
      | XI p0 ->
        (match p0 with
         | XI p1 ->
           (match p1 with
            | XI p2 ->
              (match p2 with
               | XI p3 ->
                 (match p3 with
                  | XI p4 ->
                    (match p4 with
                     | XI p5 ->
                       (match p5 with
                        | XI p6 ->
                          (match p6 with
                           | XH ->
                             (match l with
                              | [] -> false
                              | b0::l0 ->
                                (match b0 with
                                 | N0 -> false
                                 | Npos p7 ->
                                   (match p7 with
                                    | XI p8 ->
                                      (match p8 with
                                       | XI p9 ->
                                         (match p9 with
                                          | XI p10 ->
                                            (match p10 with
                                             | XI p11 ->
                                               (match p11 with
                                                | XI p12 ->
                                                  (match p12 with
                                                   | XI p13 ->
                                                     (match p13 with
                                                      | XI p14 ->
                                                        (match p14 with
                                                         | XH ->
                                                           (match l0 with
                                                            | [] -> false
                                                            | b1::l1 ->
                                                              (match b1 with
                                                               | N0 -> false
                                                               | Npos p15 ->
                                                                 (match p15 with
                                                                  | XI p16 ->
                                                                    (match p16 with
                                                                    | XI p17 ->
                                                                    (match p17 with
                                                                    | XI p18 ->
                                                                    (match p18 with
                                                                    | XI p19 ->
                                                                    (match p19 with
                                                                    | XI p20 ->
                                                                    (match p20 with
                                                                    | XI p21 ->
                                                                    (match p21 with
                                                                    | XI p22 ->
                                                                    (match p22 with
                                                                    | XH ->
                                                                    (match l1 with
                                                                    | [] ->
                                                                    false
                                                                    | b2::l2 ->
                                                                    (match b2 with
                                                                    | N0 ->
                                                                    false
                                                                    | Npos p23 ->
                                                                    (match p23 with
                                                                    | XI p24 ->
                                                                    (match p24 with
                                                                    | XI p25 ->
                                                                    (match p25 with
                                                                    | XI p26 ->
                                                                    (match p26 with
                                                                    | XI p27 ->
                                                                    (match p27 with
                                                                    | XI p28 ->
                                                                    (match p28 with
                                                                    | XI p29 ->
                                                                    (match p29 with
                                                                    | XI p30 ->
                                                                    (match p30 with
                                                                    | XH ->
                                                                    (match l2 with
                                                                    | [] ->
                                                                    false
                                                                    | b3::l3 ->
                                                                    (match b3 with
                                                                    | N0 ->
                                                                    false
                                                                    | Npos p31 ->
                                                                    (match p31 with
                                                                    | XI p32 ->
                                                                    (match p32 with
                                                                    | XI p33 ->
                                                                    (match p33 with
                                                                    | XI p34 ->
                                                                    (match p34 with
                                                                    | XI p35 ->
                                                                    (match p35 with
                                                                    | XI p36 ->
                                                                    (match p36 with
                                                                    | XI p37 ->
                                                                    (match p37 with
                                                                    | XI p38 ->
                                                                    (match p38 with
                                                                    | XH ->
                                                                    (match l3 with
                                                                    | [] ->
                                                                    false
                                                                    | b4::l4 ->
                                                                    (match b4 with
                                                                    | N0 ->
                                                                    false
                                                                    | Npos p39 ->
                                                                    (match p39 with
                                                                    | XI p40 ->
                                                                    (match p40 with
                                                                    | XI p41 ->
                                                                    (match p41 with
                                                                    | XI p42 ->
                                                                    (match p42 with
                                                                    | XI p43 ->
                                                                    (match p43 with
                                                                    | XI p44 ->
                                                                    (match p44 with
                                                                    | XI p45 ->
                                                                    (match p45 with
                                                                    | XI p46 ->
                                                                    (match p46 with
                                                                    | XH ->
                                                                    (match l4 with
                                                                    | [] ->
                                                                    true
                                                                    | _::_ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)))
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)))
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)))
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                    | _ ->
                                                                    false)
                                                                  | _ -> false)))
                                                         | _ -> false)
                                                      | _ -> false)
                                                   | _ -> false)
                                                | _ -> false)
                                             | _ -> false)
                                          | _ -> false)
                                       | _ -> false)
                                    | _ -> false)))
                           | _ -> false)
                        | _ -> false)
                     | _ -> false)
                  | _ -> false)
               | _ -> false)
            | _ -> false)
         | _ -> false)
      | _ -> false))

(** val is_multicast_mac : mACAddress -> bool **)

let is_multicast_mac = function
| [] -> false
| b0::_ -> N.testbit b0 N0

(** val is_zero_ipv4 : iPv4Address -> bool **)

let is_zero_ipv4 ip =
  if if if N.eqb ip.ipv4_a N0 then N.eqb ip.ipv4_b N0 else false
     then N.eqb ip.ipv4_c N0
     else false
  then N.eqb ip.ipv4_d N0
  else false

(** val mac_eq : mACAddress -> mACAddress -> bool **)

let mac_eq m1 m2 =
  match list_eq_dec N.eq_dec m1 m2 with
  | Left -> true
  | Right -> false

type aRPPacket = { ar_hrd : word16; ar_pro : word16; ar_hln : byte;
                   ar_pln : byte; ar_op : word16; ar_sha : byte list;
                   ar_spa : byte list; ar_tha : byte list; ar_tpa : byte list }

type aRPEthernetIPv4 = { arp_op : word16; arp_sha : mACAddress;
                         arp_spa : iPv4Address; arp_tha : mACAddress;
                         arp_tpa : iPv4Address }

type aRPCacheEntry = { ace_ip : iPv4Address; ace_mac : mACAddress;
                       ace_ttl : n; ace_static : bool }

type aRPCache = aRPCacheEntry list

(** val ip_eq : iPv4Address -> iPv4Address -> bool **)

let ip_eq ip1 ip2 =
  if if if N.eqb ip1.ipv4_a ip2.ipv4_a
        then N.eqb ip1.ipv4_b ip2.ipv4_b
        else false
     then N.eqb ip1.ipv4_c ip2.ipv4_c
     else false
  then N.eqb ip1.ipv4_d ip2.ipv4_d
  else false

(** val lookup_cache : aRPCache -> iPv4Address -> mACAddress option **)

let rec lookup_cache cache ip =
  match cache with
  | [] -> None
  | entry::rest ->
    if ip_eq entry.ace_ip ip then Some entry.ace_mac else lookup_cache rest ip

(** val update_cache_entry :
    aRPCache -> iPv4Address -> mACAddress -> n -> aRPCache **)

let update_cache_entry cache ip mac ttl =
  let entry = { ace_ip = ip; ace_mac = mac; ace_ttl = ttl; ace_static =
    false }
  in
  let rec update = function
  | [] -> []
  | e::rest ->
    if ip_eq e.ace_ip ip
    then if e.ace_static then e::rest else entry::rest
    else e::(update rest)
  in update cache

(** val add_cache_entry :
    aRPCache -> iPv4Address -> mACAddress -> n -> aRPCache **)

let add_cache_entry cache ip mac ttl =
  let entry = { ace_ip = ip; ace_mac = mac; ace_ttl = ttl; ace_static =
    false }
  in
  let rec add0 = function
  | [] -> entry::[]
  | e::rest -> if ip_eq e.ace_ip ip then e::rest else e::(add0 rest)
  in add0 cache

(** val merge_cache_entry :
    aRPCache -> iPv4Address -> mACAddress -> n -> aRPCache **)

let merge_cache_entry cache ip mac ttl =
  let entry = { ace_ip = ip; ace_mac = mac; ace_ttl = ttl; ace_static =
    false }
  in
  let rec update = function
  | [] -> entry::[]
  | e::rest ->
    if ip_eq e.ace_ip ip
    then if e.ace_static then e::rest else entry::rest
    else e::(update rest)
  in update cache

(** val rfc826_merge :
    aRPCache -> iPv4Address -> mACAddress -> n -> bool -> aRPCache **)

let rfc826_merge cache ip mac ttl i_am_target =
  match lookup_cache cache ip with
  | Some _ -> update_cache_entry cache ip mac ttl
  | None -> if i_am_target then add_cache_entry cache ip mac ttl else cache

(** val add_static_entry :
    aRPCache -> iPv4Address -> mACAddress -> aRPCache **)

let add_static_entry cache ip mac =
  let static_entry = { ace_ip = ip; ace_mac = mac; ace_ttl = N0; ace_static =
    true }
  in
  let rec add_or_update = function
  | [] -> static_entry::[]
  | e::rest ->
    if ip_eq e.ace_ip ip then static_entry::rest else e::(add_or_update rest)
  in add_or_update cache

(** val is_static_cache_entry : aRPCache -> iPv4Address -> bool **)

let rec is_static_cache_entry cache ip =
  match cache with
  | [] -> false
  | e::rest ->
    if ip_eq e.ace_ip ip then e.ace_static else is_static_cache_entry rest ip

(** val list_static_entries : aRPCache -> aRPCacheEntry list **)

let list_static_entries cache =
  filter (fun e -> e.ace_static) cache

(** val count_static_entries : aRPCache -> nat **)

let count_static_entries cache =
  length (list_static_entries cache)

(** val would_conflict_static_entry :
    aRPCache -> iPv4Address -> mACAddress -> bool **)

let would_conflict_static_entry cache ip mac =
  match lookup_cache cache ip with
  | Some existing_mac ->
    if mac_eq existing_mac mac then false else is_static_cache_entry cache ip
  | None -> false

(** val make_arp_request :
    mACAddress -> iPv4Address -> iPv4Address -> aRPEthernetIPv4 **)

let make_arp_request my_mac my_ip target_ip =
  { arp_op = aRP_OP_REQUEST; arp_sha = my_mac; arp_spa = my_ip; arp_tha =
    mAC_ZERO; arp_tpa = target_ip }

(** val make_arp_reply :
    mACAddress -> iPv4Address -> mACAddress -> iPv4Address -> aRPEthernetIPv4 **)

let make_arp_reply my_mac my_ip requester_mac requester_ip =
  { arp_op = aRP_OP_REPLY; arp_sha = my_mac; arp_spa = my_ip; arp_tha =
    requester_mac; arp_tpa = requester_ip }

(** val serialize_mac : mACAddress -> byte list **)

let serialize_mac m =
  m

(** val serialize_ipv4 : iPv4Address -> byte list **)

let serialize_ipv4 ip =
  ip.ipv4_a::(ip.ipv4_b::(ip.ipv4_c::(ip.ipv4_d::[])))

(** val split_word16 : word16 -> byte list **)

let split_word16 w =
  (N.shiftr w (Npos (XO (XO (XO XH)))))::((N.coq_land w (Npos (XI (XI (XI (XI
                                            (XI (XI (XI XH)))))))))::[])

(** val combine_word16 : byte -> byte -> word16 **)

let combine_word16 hi lo =
  N.coq_lor (N.shiftl hi (Npos (XO (XO (XO XH))))) lo

(** val serialize_arp_packet : aRPEthernetIPv4 -> byte list **)

let serialize_arp_packet p =
  app (split_word16 aRP_HRD_ETHERNET)
    (app (split_word16 aRP_PRO_IP)
      (app (eTHERNET_ADDR_LEN::[])
        (app (iPV4_ADDR_LEN::[])
          (app (split_word16 p.arp_op)
            (app (serialize_mac p.arp_sha)
              (app (serialize_ipv4 p.arp_spa)
                (app (serialize_mac p.arp_tha) (serialize_ipv4 p.arp_tpa))))))))

(** val parse_arp_packet : byte list -> aRPEthernetIPv4 option **)

let parse_arp_packet = function
| [] -> None
| hrd_hi::l ->
  (match l with
   | [] -> None
   | hrd_lo::l0 ->
     (match l0 with
      | [] -> None
      | pro_hi::l1 ->
        (match l1 with
         | [] -> None
         | pro_lo::l2 ->
           (match l2 with
            | [] -> None
            | hln::l3 ->
              (match l3 with
               | [] -> None
               | pln::l4 ->
                 (match l4 with
                  | [] -> None
                  | op_hi::l5 ->
                    (match l5 with
                     | [] -> None
                     | op_lo::l6 ->
                       (match l6 with
                        | [] -> None
                        | sha1::l7 ->
                          (match l7 with
                           | [] -> None
                           | sha2::l8 ->
                             (match l8 with
                              | [] -> None
                              | sha3::l9 ->
                                (match l9 with
                                 | [] -> None
                                 | sha4::l10 ->
                                   (match l10 with
                                    | [] -> None
                                    | sha5::l11 ->
                                      (match l11 with
                                       | [] -> None
                                       | sha6::l12 ->
                                         (match l12 with
                                          | [] -> None
                                          | spa1::l13 ->
                                            (match l13 with
                                             | [] -> None
                                             | spa2::l14 ->
                                               (match l14 with
                                                | [] -> None
                                                | spa3::l15 ->
                                                  (match l15 with
                                                   | [] -> None
                                                   | spa4::l16 ->
                                                     (match l16 with
                                                      | [] -> None
                                                      | tha1::l17 ->
                                                        (match l17 with
                                                         | [] -> None
                                                         | tha2::l18 ->
                                                           (match l18 with
                                                            | [] -> None
                                                            | tha3::l19 ->
                                                              (match l19 with
                                                               | [] -> None
                                                               | tha4::l20 ->
                                                                 (match l20 with
                                                                  | [] -> None
                                                                  | tha5::l21 ->
                                                                    (match l21 with
                                                                    | [] ->
                                                                    None
                                                                    | tha6::l22 ->
                                                                    (match l22 with
                                                                    | [] ->
                                                                    None
                                                                    | tpa1::l23 ->
                                                                    (match l23 with
                                                                    | [] ->
                                                                    None
                                                                    | tpa2::l24 ->
                                                                    (match l24 with
                                                                    | [] ->
                                                                    None
                                                                    | tpa3::l25 ->
                                                                    (match l25 with
                                                                    | [] ->
                                                                    None
                                                                    | tpa4::l26 ->
                                                                    (match l26 with
                                                                    | [] ->
                                                                    if 
                                                                    if 
                                                                    if 
                                                                    if 
                                                                    N.eqb
                                                                    (combine_word16
                                                                    hrd_hi
                                                                    hrd_lo)
                                                                    aRP_HRD_ETHERNET
                                                                    then 
                                                                    N.eqb
                                                                    (combine_word16
                                                                    pro_hi
                                                                    pro_lo)
                                                                    aRP_PRO_IP
                                                                    else false
                                                                    then 
                                                                    N.eqb hln
                                                                    eTHERNET_ADDR_LEN
                                                                    else false
                                                                    then 
                                                                    N.eqb pln
                                                                    iPV4_ADDR_LEN
                                                                    else false
                                                                    then 
                                                                    Some
                                                                    { arp_op =
                                                                    (combine_word16
                                                                    op_hi
                                                                    op_lo);
                                                                    arp_sha =
                                                                    (sha1::(sha2::(sha3::(sha4::(sha5::(sha6::[]))))));
                                                                    arp_spa =
                                                                    { ipv4_a =
                                                                    spa1;
                                                                    ipv4_b =
                                                                    spa2;
                                                                    ipv4_c =
                                                                    spa3;
                                                                    ipv4_d =
                                                                    spa4 };
                                                                    arp_tha =
                                                                    (tha1::(tha2::(tha3::(tha4::(tha5::(tha6::[]))))));
                                                                    arp_tpa =
                                                                    { ipv4_a =
                                                                    tpa1;
                                                                    ipv4_b =
                                                                    tpa2;
                                                                    ipv4_c =
                                                                    tpa3;
                                                                    ipv4_d =
                                                                    tpa4 } }
                                                                    else None
                                                                    | _::_ ->
                                                                    None))))))))))))))))))))))))))))

(** val is_supported_hw_proto : word16 -> word16 -> bool **)

let is_supported_hw_proto hrd pro =
  if N.eqb hrd aRP_HRD_ETHERNET then N.eqb pro aRP_PRO_IP else false

(** val process_generic_arp : aRPPacket -> aRPEthernetIPv4 option **)

let process_generic_arp packet =
  if is_supported_hw_proto packet.ar_hrd packet.ar_pro
  then if if N.eqb packet.ar_hln eTHERNET_ADDR_LEN
          then N.eqb packet.ar_pln iPV4_ADDR_LEN
          else false
       then (match packet.ar_sha with
             | [] -> None
             | sha1::l ->
               (match l with
                | [] -> None
                | sha2::l0 ->
                  (match l0 with
                   | [] -> None
                   | sha3::l1 ->
                     (match l1 with
                      | [] -> None
                      | sha4::l2 ->
                        (match l2 with
                         | [] -> None
                         | sha5::l3 ->
                           (match l3 with
                            | [] -> None
                            | sha6::l4 ->
                              (match l4 with
                               | [] ->
                                 (match packet.ar_spa with
                                  | [] -> None
                                  | spa1::l5 ->
                                    (match l5 with
                                     | [] -> None
                                     | spa2::l6 ->
                                       (match l6 with
                                        | [] -> None
                                        | spa3::l7 ->
                                          (match l7 with
                                           | [] -> None
                                           | spa4::l8 ->
                                             (match l8 with
                                              | [] ->
                                                (match packet.ar_tha with
                                                 | [] -> None
                                                 | tha1::l9 ->
                                                   (match l9 with
                                                    | [] -> None
                                                    | tha2::l10 ->
                                                      (match l10 with
                                                       | [] -> None
                                                       | tha3::l11 ->
                                                         (match l11 with
                                                          | [] -> None
                                                          | tha4::l12 ->
                                                            (match l12 with
                                                             | [] -> None
                                                             | tha5::l13 ->
                                                               (match l13 with
                                                                | [] -> None
                                                                | tha6::l14 ->
                                                                  (match l14 with
                                                                   | [] ->
                                                                    (match packet.ar_tpa with
                                                                    | [] ->
                                                                    None
                                                                    | tpa1::l15 ->
                                                                    (match l15 with
                                                                    | [] ->
                                                                    None
                                                                    | tpa2::l16 ->
                                                                    (match l16 with
                                                                    | [] ->
                                                                    None
                                                                    | tpa3::l17 ->
                                                                    (match l17 with
                                                                    | [] ->
                                                                    None
                                                                    | tpa4::l18 ->
                                                                    (match l18 with
                                                                    | [] ->
                                                                    Some
                                                                    { arp_op =
                                                                    packet.ar_op;
                                                                    arp_sha =
                                                                    (sha1::(sha2::(sha3::(sha4::(sha5::(sha6::[]))))));
                                                                    arp_spa =
                                                                    { ipv4_a =
                                                                    spa1;
                                                                    ipv4_b =
                                                                    spa2;
                                                                    ipv4_c =
                                                                    spa3;
                                                                    ipv4_d =
                                                                    spa4 };
                                                                    arp_tha =
                                                                    (tha1::(tha2::(tha3::(tha4::(tha5::(tha6::[]))))));
                                                                    arp_tpa =
                                                                    { ipv4_a =
                                                                    tpa1;
                                                                    ipv4_b =
                                                                    tpa2;
                                                                    ipv4_c =
                                                                    tpa3;
                                                                    ipv4_d =
                                                                    tpa4 } }
                                                                    | _::_ ->
                                                                    None)))))
                                                                   | _::_ ->
                                                                    None)))))))
                                              | _::_ -> None)))))
                               | _::_ -> None)))))))
       else None
  else None

(** val convert_to_generic : aRPEthernetIPv4 -> aRPPacket **)

let convert_to_generic packet =
  { ar_hrd = aRP_HRD_ETHERNET; ar_pro = aRP_PRO_IP; ar_hln =
    eTHERNET_ADDR_LEN; ar_pln = iPV4_ADDR_LEN; ar_op = packet.arp_op;
    ar_sha = (serialize_mac packet.arp_sha); ar_spa =
    (serialize_ipv4 packet.arp_spa); ar_tha = (serialize_mac packet.arp_tha);
    ar_tpa = (serialize_ipv4 packet.arp_tpa) }

type aRPError =
| ErrInvalidOpcode of word16
| ErrBroadcastSender
| ErrMulticastSender
| ErrZeroSPANonRequest
| ErrReplyWrongTHA of mACAddress * mACAddress
| ErrCacheFull of nat
| ErrFloodLimitExceeded of iPv4Address * n
| ErrStaticEntryConflict of iPv4Address
| ErrDuplicateIP of iPv4Address * mACAddress
| ErrInvalidPacketLength of nat
| ErrUnsupportedHardware of word16
| ErrUnsupportedProtocol of word16

type 'a aRPResult =
| ARPSuccess of 'a
| ARPFailure of aRPError

(** val validate_arp_packet : aRPEthernetIPv4 -> mACAddress -> bool **)

let validate_arp_packet packet my_mac =
  if if if if is_valid_arp_opcode packet.arp_op
           then negb (is_broadcast_mac packet.arp_sha)
           else false
        then negb (is_multicast_mac packet.arp_sha)
        else false
     then if negb (is_zero_ipv4 packet.arp_spa)
          then true
          else N.eqb packet.arp_op aRP_OP_REQUEST
     else false
  then if negb (N.eqb packet.arp_op aRP_OP_REPLY)
       then true
       else mac_eq packet.arp_tha my_mac
  else false

(** val validate_arp_packet_detailed :
    aRPEthernetIPv4 -> mACAddress -> unit0 aRPResult **)

let validate_arp_packet_detailed packet my_mac =
  if negb (is_valid_arp_opcode packet.arp_op)
  then ARPFailure (ErrInvalidOpcode packet.arp_op)
  else if is_broadcast_mac packet.arp_sha
       then ARPFailure ErrBroadcastSender
       else if is_multicast_mac packet.arp_sha
            then ARPFailure ErrMulticastSender
            else if is_zero_ipv4 packet.arp_spa
                 then if negb (N.eqb packet.arp_op aRP_OP_REQUEST)
                      then ARPFailure ErrZeroSPANonRequest
                      else ARPSuccess Tt
                 else if N.eqb packet.arp_op aRP_OP_REPLY
                      then if negb (mac_eq packet.arp_tha my_mac)
                           then ARPFailure (ErrReplyWrongTHA (packet.arp_tha,
                                  my_mac))
                           else ARPSuccess Tt
                      else ARPSuccess Tt

type validatedARPPacket =
  aRPEthernetIPv4
  (* singleton inductive, whose constructor was Build_ValidatedARPPacket *)

(** val mk_validated_arp :
    mACAddress -> aRPEthernetIPv4 -> validatedARPPacket option **)

let mk_validated_arp my_mac packet =
  match bool_dec (validate_arp_packet packet my_mac) true with
  | Left -> Some packet
  | Right -> None

(** val dEFAULT_ARP_TTL : n **)

let dEFAULT_ARP_TTL =
  Npos (XO (XO (XI (XI (XO (XI (XO (XO XH))))))))

type aRPContext = { arp_my_mac : mACAddress; arp_my_ip : iPv4Address;
                    arp_cache : aRPCache; arp_cache_ttl : n }

type gratuitousARPType =
| NotGratuitous
| GratuitousRequest
| GratuitousReply

(** val is_gratuitous_arp : aRPEthernetIPv4 -> bool **)

let is_gratuitous_arp pkt =
  ip_eq pkt.arp_spa pkt.arp_tpa

(** val classify_gratuitous_arp : aRPEthernetIPv4 -> gratuitousARPType **)

let classify_gratuitous_arp pkt =
  if ip_eq pkt.arp_spa pkt.arp_tpa
  then if N.eqb pkt.arp_op aRP_OP_REQUEST
       then GratuitousRequest
       else if N.eqb pkt.arp_op aRP_OP_REPLY
            then GratuitousReply
            else NotGratuitous
  else NotGratuitous

(** val is_gratuitous_request : aRPEthernetIPv4 -> bool **)

let is_gratuitous_request pkt =
  match classify_gratuitous_arp pkt with
  | GratuitousRequest -> true
  | _ -> false

(** val is_gratuitous_reply : aRPEthernetIPv4 -> bool **)

let is_gratuitous_reply pkt =
  match classify_gratuitous_arp pkt with
  | GratuitousReply -> true
  | _ -> false

(** val flush_cache : aRPCache **)

let flush_cache =
  []

(** val flush_dynamic_entries : aRPCache -> aRPCache **)

let flush_dynamic_entries cache =
  filter (fun e -> e.ace_static) cache

(** val update_cache_ttl : aRPCache -> n -> aRPCache **)

let update_cache_ttl cache new_ttl =
  map (fun e ->
    if e.ace_static
    then e
    else { ace_ip = e.ace_ip; ace_mac = e.ace_mac; ace_ttl = new_ttl;
           ace_static = e.ace_static }) cache

(** val set_context_ttl : aRPContext -> n -> aRPContext **)

let set_context_ttl ctx new_ttl =
  { arp_my_mac = ctx.arp_my_mac; arp_my_ip = ctx.arp_my_ip; arp_cache =
    ctx.arp_cache; arp_cache_ttl = new_ttl }

(** val flush_context_cache : aRPContext -> aRPContext **)

let flush_context_cache ctx =
  { arp_my_mac = ctx.arp_my_mac; arp_my_ip = ctx.arp_my_ip; arp_cache =
    flush_cache; arp_cache_ttl = ctx.arp_cache_ttl }

(** val flush_context_dynamic : aRPContext -> aRPContext **)

let flush_context_dynamic ctx =
  { arp_my_mac = ctx.arp_my_mac; arp_my_ip = ctx.arp_my_ip; arp_cache =
    (flush_dynamic_entries ctx.arp_cache); arp_cache_ttl = ctx.arp_cache_ttl }

(** val get_cache_size : aRPCache -> nat **)

let get_cache_size =
  length

(** val get_static_count : aRPCache -> nat **)

let get_static_count =
  count_static_entries

(** val get_dynamic_count : aRPCache -> nat **)

let get_dynamic_count cache =
  length (filter (fun e -> negb e.ace_static) cache)

(** val process_arp_packet :
    aRPContext -> aRPEthernetIPv4 -> aRPContext*aRPEthernetIPv4 option **)

let process_arp_packet ctx packet =
  if validate_arp_packet packet ctx.arp_my_mac
  then let i_am_target = ip_eq packet.arp_tpa ctx.arp_my_ip in
       let cache' =
         rfc826_merge ctx.arp_cache packet.arp_spa packet.arp_sha
           ctx.arp_cache_ttl i_am_target
       in
       let ctx' = { arp_my_mac = ctx.arp_my_mac; arp_my_ip = ctx.arp_my_ip;
         arp_cache = cache'; arp_cache_ttl = ctx.arp_cache_ttl }
       in
       if i_am_target
       then if N.eqb packet.arp_op aRP_OP_REQUEST
            then if is_gratuitous_arp packet
                 then ctx',None
                 else let reply =
                        make_arp_reply ctx.arp_my_mac ctx.arp_my_ip
                          packet.arp_sha packet.arp_spa
                      in
                      ctx',(Some reply)
            else ctx',None
       else ctx',None
  else ctx,None

(** val process_validated_arp_packet :
    aRPContext -> validatedARPPacket -> aRPContext*aRPEthernetIPv4 option **)

let process_validated_arp_packet ctx vpacket =
  let i_am_target = ip_eq vpacket.arp_tpa ctx.arp_my_ip in
  let cache' =
    rfc826_merge ctx.arp_cache vpacket.arp_spa vpacket.arp_sha
      ctx.arp_cache_ttl i_am_target
  in
  let ctx' = { arp_my_mac = ctx.arp_my_mac; arp_my_ip = ctx.arp_my_ip;
    arp_cache = cache'; arp_cache_ttl = ctx.arp_cache_ttl }
  in
  if i_am_target
  then if N.eqb vpacket.arp_op aRP_OP_REQUEST
       then if is_gratuitous_arp vpacket
            then ctx',None
            else let reply =
                   make_arp_reply ctx.arp_my_mac ctx.arp_my_ip
                     vpacket.arp_sha vpacket.arp_spa
                 in
                 ctx',(Some reply)
       else ctx',None
  else ctx',None

(** val parse_validated_arp_packet :
    mACAddress -> byte list -> validatedARPPacket option **)

let parse_validated_arp_packet my_mac data =
  match parse_arp_packet data with
  | Some packet -> mk_validated_arp my_mac packet
  | None -> None

type rARPMapping = { rarp_mac : mACAddress; rarp_ip : iPv4Address }

type rARPTable = rARPMapping list

(** val lookup_rarp_table : rARPTable -> mACAddress -> iPv4Address option **)

let rec lookup_rarp_table table mac =
  match table with
  | [] -> None
  | entry::rest ->
    if mac_eq entry.rarp_mac mac
    then Some entry.rarp_ip
    else lookup_rarp_table rest mac

(** val validate_rarp_client : aRPEthernetIPv4 -> mACAddress -> bool **)

let validate_rarp_client packet my_mac =
  if if if N.eqb packet.arp_op rARP_OP_REPLY
        then mac_eq packet.arp_tha my_mac
        else false
     then negb (is_broadcast_mac packet.arp_sha)
     else false
  then negb (is_multicast_mac packet.arp_sha)
  else false

(** val validate_rarp_server : aRPEthernetIPv4 -> bool **)

let validate_rarp_server packet =
  if if if N.eqb packet.arp_op rARP_OP_REQUEST
        then negb (is_broadcast_mac packet.arp_sha)
        else false
     then negb (is_multicast_mac packet.arp_sha)
     else false
  then is_zero_ipv4 packet.arp_spa
  else false

(** val validate_rarp_packet : aRPEthernetIPv4 -> mACAddress -> bool **)

let validate_rarp_packet packet my_mac =
  if validate_rarp_client packet my_mac
  then true
  else validate_rarp_server packet

(** val process_rarp_client :
    aRPContext -> aRPEthernetIPv4 -> aRPContext*iPv4Address option **)

let process_rarp_client ctx packet =
  if validate_rarp_client packet ctx.arp_my_mac
  then ctx,(Some packet.arp_tpa)
  else ctx,None

(** val process_rarp_server :
    aRPContext -> rARPTable -> aRPEthernetIPv4 -> aRPContext*aRPEthernetIPv4
    option **)

let process_rarp_server ctx table packet =
  if validate_rarp_server packet
  then (match lookup_rarp_table table packet.arp_tha with
        | Some assigned_ip ->
          let reply = { arp_op = rARP_OP_REPLY; arp_sha = ctx.arp_my_mac;
            arp_spa = ctx.arp_my_ip; arp_tha = packet.arp_tha; arp_tpa =
            assigned_ip }
          in
          ctx,(Some reply)
        | None -> ctx,None)
  else ctx,None

(** val process_rarp_packet :
    aRPContext -> aRPEthernetIPv4 -> aRPContext*iPv4Address option **)

let process_rarp_packet =
  process_rarp_client

type validatedRARPClient =
  aRPEthernetIPv4
  (* singleton inductive, whose constructor was Build_ValidatedRARPClient *)

type validatedRARPServer =
  aRPEthernetIPv4
  (* singleton inductive, whose constructor was Build_ValidatedRARPServer *)

(** val mk_validated_rarp_client :
    mACAddress -> aRPEthernetIPv4 -> validatedRARPClient option **)

let mk_validated_rarp_client my_mac packet =
  match bool_dec (validate_rarp_client packet my_mac) true with
  | Left -> Some packet
  | Right -> None

(** val mk_validated_rarp_server :
    aRPEthernetIPv4 -> validatedRARPServer option **)

let mk_validated_rarp_server packet =
  match bool_dec (validate_rarp_server packet) true with
  | Left -> Some packet
  | Right -> None

(** val make_gratuitous_arp : mACAddress -> iPv4Address -> aRPEthernetIPv4 **)

let make_gratuitous_arp my_mac my_ip =
  { arp_op = aRP_OP_REQUEST; arp_sha = my_mac; arp_spa = my_ip; arp_tha =
    mAC_ZERO; arp_tpa = my_ip }

(** val is_suspicious_arp : aRPCache -> aRPEthernetIPv4 -> bool **)

let is_suspicious_arp cache packet =
  match lookup_cache cache packet.arp_spa with
  | Some cached_mac ->
    (match list_eq_dec N.eq_dec cached_mac packet.arp_sha with
     | Left -> false
     | Right -> true)
  | None -> false

(** val aRP_REQUEST_TIMEOUT : n **)

let aRP_REQUEST_TIMEOUT =
  Npos (XO (XO (XO (XI (XO (XI (XI (XI (XI XH)))))))))

(** val aRP_MAX_RETRIES : n **)

let aRP_MAX_RETRIES =
  Npos (XI XH)

(** val aRP_PROBE_WAIT : n **)

let aRP_PROBE_WAIT =
  Npos (XO (XO (XO (XI (XO (XI (XI (XI (XI XH)))))))))

(** val aRP_PROBE_NUM : n **)

let aRP_PROBE_NUM =
  Npos (XI XH)

(** val aRP_PROBE_MIN : n **)

let aRP_PROBE_MIN =
  Npos (XO (XO (XO (XI (XO (XI (XI (XI (XI XH)))))))))

(** val aRP_ANNOUNCE_WAIT : n **)

let aRP_ANNOUNCE_WAIT =
  Npos (XO (XO (XO (XO (XI (XO (XI (XI (XI (XI XH))))))))))

(** val aRP_ANNOUNCE_NUM : n **)

let aRP_ANNOUNCE_NUM =
  Npos (XO XH)

(** val aRP_ANNOUNCE_INTERVAL : n **)

let aRP_ANNOUNCE_INTERVAL =
  Npos (XO (XO (XO (XO (XI (XO (XI (XI (XI (XI XH))))))))))

(** val aRP_DEFEND_INTERVAL : n **)

let aRP_DEFEND_INTERVAL =
  Npos (XO (XO (XO (XO (XI (XO (XO (XO (XI (XI (XI (XO (XO XH)))))))))))))

(** val aRP_CONFLICT_RECOVERY_WAIT : n **)

let aRP_CONFLICT_RECOVERY_WAIT =
  Npos (XO (XO (XO (XO (XI (XO (XO (XO (XI (XI (XI (XO (XO XH)))))))))))))

type aRPTimer = { timer_start : n; timer_duration : n; timer_active : bool }

(** val timer_expired : aRPTimer -> n -> bool **)

let timer_expired timer current_time =
  if timer.timer_active
  then N.leb (N.add timer.timer_start timer.timer_duration) current_time
  else false

(** val start_timer : n -> n -> aRPTimer **)

let start_timer duration current_time =
  { timer_start = current_time; timer_duration = duration; timer_active =
    true }

(** val stop_timer : aRPTimer -> aRPTimer **)

let stop_timer timer =
  { timer_start = timer.timer_start; timer_duration = timer.timer_duration;
    timer_active = false }

type pendingRequest = { preq_target_ip : iPv4Address; preq_retries : 
                        n; preq_timer : aRPTimer }

type probeState = { probe_ip : iPv4Address; probe_count : n;
                    probe_timer : aRPTimer }

type announceState = { announce_count : n; announce_timer : aRPTimer }

type defendState =
  n
  (* singleton inductive, whose constructor was Build_DefendState *)

type aRPStateData =
| StateIdle
| StatePending of pendingRequest list
| StateProbe of probeState
| StateAnnounce of announceState
| StateDefend of defendState
| StateConflict of iPv4Address * aRPTimer

type networkInterface = { if_mac : mACAddress; if_ip : iPv4Address;
                          if_mtu : n; if_up : bool }

type interfaceID = n

type networkInterfaceEx = { ifex_id : interfaceID; ifex_mac : mACAddress;
                            ifex_ip : iPv4Address; ifex_mtu : n;
                            ifex_up : bool; ifex_cache : aRPCache;
                            ifex_cache_ttl : n; ifex_state_data : aRPStateData }

type interfaceTable = networkInterfaceEx list

type floodEntry = { fe_ip : iPv4Address; fe_last_request : n;
                    fe_request_count : n }

type floodTable = floodEntry list

type multiInterfaceARPContext = { mi_interfaces : interfaceTable;
                                  mi_global_flood_table : floodTable;
                                  mi_last_cleanup : n }

(** val lookup_interface :
    interfaceTable -> interfaceID -> networkInterfaceEx option **)

let rec lookup_interface table id =
  match table with
  | [] -> None
  | iface::rest ->
    if N.eqb iface.ifex_id id then Some iface else lookup_interface rest id

(** val lookup_interface_by_mac :
    interfaceTable -> mACAddress -> networkInterfaceEx option **)

let rec lookup_interface_by_mac table mac =
  match table with
  | [] -> None
  | iface::rest ->
    if mac_eq iface.ifex_mac mac
    then Some iface
    else lookup_interface_by_mac rest mac

(** val lookup_interface_by_ip :
    interfaceTable -> iPv4Address -> networkInterfaceEx option **)

let rec lookup_interface_by_ip table ip =
  match table with
  | [] -> None
  | iface::rest ->
    if ip_eq iface.ifex_ip ip
    then Some iface
    else lookup_interface_by_ip rest ip

(** val is_local_ip : interfaceTable -> iPv4Address -> bool **)

let is_local_ip table ip =
  match lookup_interface_by_ip table ip with
  | Some _ -> true
  | None -> false

(** val select_interface_for_target :
    interfaceTable -> iPv4Address -> networkInterfaceEx option **)

let rec select_interface_for_target table target_ip =
  match table with
  | [] -> None
  | iface::rest ->
    if iface.ifex_up
    then Some iface
    else select_interface_for_target rest target_ip

(** val get_up_interfaces : interfaceTable -> interfaceTable **)

let rec get_up_interfaces table =
  filter (fun iface -> iface.ifex_up) table

(** val count_interfaces : interfaceTable -> nat **)

let count_interfaces =
  length

(** val count_up_interfaces : interfaceTable -> nat **)

let count_up_interfaces table =
  length (get_up_interfaces table)

(** val update_interface :
    interfaceTable -> networkInterfaceEx -> interfaceTable **)

let rec update_interface table updated =
  match table with
  | [] -> updated::[]
  | iface::rest ->
    if N.eqb iface.ifex_id updated.ifex_id
    then updated::rest
    else iface::(update_interface rest updated)

(** val update_interface_cache :
    networkInterfaceEx -> aRPCache -> networkInterfaceEx **)

let update_interface_cache iface cache =
  { ifex_id = iface.ifex_id; ifex_mac = iface.ifex_mac; ifex_ip =
    iface.ifex_ip; ifex_mtu = iface.ifex_mtu; ifex_up = iface.ifex_up;
    ifex_cache = cache; ifex_cache_ttl = iface.ifex_cache_ttl;
    ifex_state_data = iface.ifex_state_data }

(** val update_interface_state :
    networkInterfaceEx -> aRPStateData -> networkInterfaceEx **)

let update_interface_state iface state =
  { ifex_id = iface.ifex_id; ifex_mac = iface.ifex_mac; ifex_ip =
    iface.ifex_ip; ifex_mtu = iface.ifex_mtu; ifex_up = iface.ifex_up;
    ifex_cache = iface.ifex_cache; ifex_cache_ttl = iface.ifex_cache_ttl;
    ifex_state_data = state }

(** val set_interface_up :
    networkInterfaceEx -> bool -> networkInterfaceEx **)

let set_interface_up iface up =
  { ifex_id = iface.ifex_id; ifex_mac = iface.ifex_mac; ifex_ip =
    iface.ifex_ip; ifex_mtu = iface.ifex_mtu; ifex_up = up; ifex_cache =
    iface.ifex_cache; ifex_cache_ttl = iface.ifex_cache_ttl;
    ifex_state_data = iface.ifex_state_data }

(** val remove_interface : interfaceTable -> interfaceID -> interfaceTable **)

let rec remove_interface table id =
  match table with
  | [] -> []
  | iface::rest ->
    if N.eqb iface.ifex_id id then rest else iface::(remove_interface rest id)

(** val add_interface :
    interfaceTable -> networkInterfaceEx -> interfaceTable **)

let add_interface table new_iface =
  new_iface::table

(** val process_arp_packet_on_interface :
    networkInterfaceEx -> aRPEthernetIPv4 ->
    networkInterfaceEx*aRPEthernetIPv4 option **)

let process_arp_packet_on_interface iface packet =
  if validate_arp_packet packet iface.ifex_mac
  then let i_am_target = ip_eq packet.arp_tpa iface.ifex_ip in
       let cache' =
         rfc826_merge iface.ifex_cache packet.arp_spa packet.arp_sha
           iface.ifex_cache_ttl i_am_target
       in
       let iface' = update_interface_cache iface cache' in
       if i_am_target
       then if N.eqb packet.arp_op aRP_OP_REQUEST
            then if is_gratuitous_arp packet
                 then iface',None
                 else let reply =
                        make_arp_reply iface.ifex_mac iface.ifex_ip
                          packet.arp_sha packet.arp_spa
                      in
                      iface',(Some reply)
            else iface',None
       else iface',None
  else iface,None

(** val process_arp_packet_multi :
    multiInterfaceARPContext -> aRPEthernetIPv4 ->
    multiInterfaceARPContext*(interfaceID*aRPEthernetIPv4) option **)

let process_arp_packet_multi ctx packet =
  match lookup_interface_by_ip ctx.mi_interfaces packet.arp_tpa with
  | Some iface ->
    let iface',resp = process_arp_packet_on_interface iface packet in
    let ctx' = { mi_interfaces = (update_interface ctx.mi_interfaces iface');
      mi_global_flood_table = ctx.mi_global_flood_table; mi_last_cleanup =
      ctx.mi_last_cleanup }
    in
    (match resp with
     | Some reply -> ctx',(Some (iface.ifex_id,reply))
     | None -> ctx',None)
  | None ->
    let update_all_caches = fun ifaces ->
      map (fun iface ->
        if iface.ifex_up
        then let cache' =
               rfc826_merge iface.ifex_cache packet.arp_spa packet.arp_sha
                 iface.ifex_cache_ttl false
             in
             update_interface_cache iface cache'
        else iface) ifaces
    in
    let ctx' = { mi_interfaces = (update_all_caches ctx.mi_interfaces);
      mi_global_flood_table = ctx.mi_global_flood_table; mi_last_cleanup =
      ctx.mi_last_cleanup }
    in
    ctx',None

(** val send_arp_request_from_interface :
    networkInterfaceEx -> iPv4Address -> aRPEthernetIPv4 **)

let send_arp_request_from_interface iface target_ip =
  make_arp_request iface.ifex_mac iface.ifex_ip target_ip

(** val check_interface_caches :
    interfaceTable -> iPv4Address -> (interfaceID*mACAddress) option **)

let rec check_interface_caches ifaces target_ip =
  match ifaces with
  | [] -> None
  | iface::rest ->
    (match lookup_cache iface.ifex_cache target_ip with
     | Some mac -> Some (iface.ifex_id,mac)
     | None -> check_interface_caches rest target_ip)

(** val resolve_address_multi :
    multiInterfaceARPContext -> iPv4Address -> (interfaceID*mACAddress)
    option*(interfaceID*aRPEthernetIPv4) option **)

let resolve_address_multi ctx target_ip =
  match check_interface_caches ctx.mi_interfaces target_ip with
  | Some result -> (Some result),None
  | None ->
    (match select_interface_for_target ctx.mi_interfaces target_ip with
     | Some iface ->
       let request = send_arp_request_from_interface iface target_ip in
       None,(Some (iface.ifex_id,request))
     | None -> None,None)

(** val create_interface :
    interfaceID -> mACAddress -> iPv4Address -> n -> networkInterfaceEx **)

let create_interface id mac ip mtu =
  { ifex_id = id; ifex_mac = mac; ifex_ip = ip; ifex_mtu = mtu; ifex_up =
    false; ifex_cache = []; ifex_cache_ttl = dEFAULT_ARP_TTL;
    ifex_state_data = StateIdle }

(** val bring_interface_up :
    multiInterfaceARPContext -> interfaceID -> multiInterfaceARPContext **)

let bring_interface_up ctx id =
  match lookup_interface ctx.mi_interfaces id with
  | Some iface ->
    let iface' = set_interface_up iface true in
    { mi_interfaces = (update_interface ctx.mi_interfaces iface');
    mi_global_flood_table = ctx.mi_global_flood_table; mi_last_cleanup =
    ctx.mi_last_cleanup }
  | None -> ctx

(** val bring_interface_down :
    multiInterfaceARPContext -> interfaceID -> multiInterfaceARPContext **)

let bring_interface_down ctx id =
  match lookup_interface ctx.mi_interfaces id with
  | Some iface ->
    let iface' = set_interface_up iface false in
    { mi_interfaces = (update_interface ctx.mi_interfaces iface');
    mi_global_flood_table = ctx.mi_global_flood_table; mi_last_cleanup =
    ctx.mi_last_cleanup }
  | None -> ctx

(** val flush_interface_cache :
    multiInterfaceARPContext -> interfaceID -> multiInterfaceARPContext **)

let flush_interface_cache ctx id =
  match lookup_interface ctx.mi_interfaces id with
  | Some iface ->
    let iface' = update_interface_cache iface [] in
    { mi_interfaces = (update_interface ctx.mi_interfaces iface');
    mi_global_flood_table = ctx.mi_global_flood_table; mi_last_cleanup =
    ctx.mi_last_cleanup }
  | None -> ctx

(** val flush_all_interface_caches :
    multiInterfaceARPContext -> multiInterfaceARPContext **)

let flush_all_interface_caches ctx =
  let flush_all =
    map (fun iface -> update_interface_cache iface []) ctx.mi_interfaces
  in
  { mi_interfaces = flush_all; mi_global_flood_table =
  ctx.mi_global_flood_table; mi_last_cleanup = ctx.mi_last_cleanup }

(** val add_interface_to_context :
    multiInterfaceARPContext -> networkInterfaceEx -> multiInterfaceARPContext **)

let add_interface_to_context ctx iface =
  { mi_interfaces = (add_interface ctx.mi_interfaces iface);
    mi_global_flood_table = ctx.mi_global_flood_table; mi_last_cleanup =
    ctx.mi_last_cleanup }

(** val remove_interface_from_context :
    multiInterfaceARPContext -> interfaceID -> multiInterfaceARPContext **)

let remove_interface_from_context ctx id =
  { mi_interfaces = (remove_interface ctx.mi_interfaces id);
    mi_global_flood_table = ctx.mi_global_flood_table; mi_last_cleanup =
    ctx.mi_last_cleanup }

(** val total_cache_entries : multiInterfaceARPContext -> nat **)

let total_cache_entries ctx =
  fold_left (fun acc iface -> add acc (length iface.ifex_cache))
    ctx.mi_interfaces O

type enhancedARPContext = { earp_my_mac : mACAddress;
                            earp_my_ip : iPv4Address; earp_cache : aRPCache;
                            earp_cache_ttl : n;
                            earp_state_data : aRPStateData;
                            earp_iface : networkInterface;
                            earp_flood_table : floodTable;
                            earp_last_cache_cleanup : n }

(** val set_enhanced_context_ttl :
    enhancedARPContext -> n -> enhancedARPContext **)

let set_enhanced_context_ttl ctx new_ttl =
  { earp_my_mac = ctx.earp_my_mac; earp_my_ip = ctx.earp_my_ip; earp_cache =
    ctx.earp_cache; earp_cache_ttl = new_ttl; earp_state_data =
    ctx.earp_state_data; earp_iface = ctx.earp_iface; earp_flood_table =
    ctx.earp_flood_table; earp_last_cache_cleanup =
    ctx.earp_last_cache_cleanup }

(** val flush_enhanced_cache : enhancedARPContext -> enhancedARPContext **)

let flush_enhanced_cache ctx =
  { earp_my_mac = ctx.earp_my_mac; earp_my_ip = ctx.earp_my_ip; earp_cache =
    flush_cache; earp_cache_ttl = ctx.earp_cache_ttl; earp_state_data =
    ctx.earp_state_data; earp_iface = ctx.earp_iface; earp_flood_table =
    ctx.earp_flood_table; earp_last_cache_cleanup =
    ctx.earp_last_cache_cleanup }

(** val flush_enhanced_dynamic : enhancedARPContext -> enhancedARPContext **)

let flush_enhanced_dynamic ctx =
  { earp_my_mac = ctx.earp_my_mac; earp_my_ip = ctx.earp_my_ip; earp_cache =
    (flush_dynamic_entries ctx.earp_cache); earp_cache_ttl =
    ctx.earp_cache_ttl; earp_state_data = ctx.earp_state_data; earp_iface =
    ctx.earp_iface; earp_flood_table = ctx.earp_flood_table;
    earp_last_cache_cleanup = ctx.earp_last_cache_cleanup }

(** val disable_dad : enhancedARPContext -> enhancedARPContext **)

let disable_dad ctx =
  { earp_my_mac = ctx.earp_my_mac; earp_my_ip = ctx.earp_my_ip; earp_cache =
    ctx.earp_cache; earp_cache_ttl = ctx.earp_cache_ttl; earp_state_data =
    StateIdle; earp_iface = ctx.earp_iface; earp_flood_table =
    ctx.earp_flood_table; earp_last_cache_cleanup =
    ctx.earp_last_cache_cleanup }

(** val reset_flood_table : enhancedARPContext -> enhancedARPContext **)

let reset_flood_table ctx =
  { earp_my_mac = ctx.earp_my_mac; earp_my_ip = ctx.earp_my_ip; earp_cache =
    ctx.earp_cache; earp_cache_ttl = ctx.earp_cache_ttl; earp_state_data =
    ctx.earp_state_data; earp_iface = ctx.earp_iface; earp_flood_table = [];
    earp_last_cache_cleanup = ctx.earp_last_cache_cleanup }

(** val single_to_multi :
    aRPContext -> interfaceID -> multiInterfaceARPContext **)

let single_to_multi ctx id =
  let iface = { ifex_id = id; ifex_mac = ctx.arp_my_mac; ifex_ip =
    ctx.arp_my_ip; ifex_mtu = (Npos (XO (XO (XI (XI (XI (XO (XI (XI (XI (XO
    XH))))))))))); ifex_up = true; ifex_cache = ctx.arp_cache;
    ifex_cache_ttl = ctx.arp_cache_ttl; ifex_state_data = StateIdle }
  in
  { mi_interfaces = (iface::[]); mi_global_flood_table = [];
  mi_last_cleanup = N0 }

(** val enhanced_to_multi :
    enhancedARPContext -> interfaceID -> multiInterfaceARPContext **)

let enhanced_to_multi ctx id =
  let iface = { ifex_id = id; ifex_mac = ctx.earp_my_mac; ifex_ip =
    ctx.earp_my_ip; ifex_mtu = ctx.earp_iface.if_mtu; ifex_up =
    ctx.earp_iface.if_up; ifex_cache = ctx.earp_cache; ifex_cache_ttl =
    ctx.earp_cache_ttl; ifex_state_data = ctx.earp_state_data }
  in
  { mi_interfaces = (iface::[]); mi_global_flood_table =
  ctx.earp_flood_table; mi_last_cleanup = ctx.earp_last_cache_cleanup }

(** val aRP_FLOOD_WINDOW : n **)

let aRP_FLOOD_WINDOW =
  Npos (XO (XO (XO (XI (XO (XI (XI (XI (XI XH)))))))))

(** val aRP_FLOOD_THRESHOLD : n **)

let aRP_FLOOD_THRESHOLD =
  Npos (XI (XO XH))

(** val flood_eq : iPv4Address -> iPv4Address -> bool **)

let flood_eq =
  ip_eq

(** val lookup_flood_entry :
    floodTable -> iPv4Address -> floodEntry option **)

let rec lookup_flood_entry table ip =
  match table with
  | [] -> None
  | entry::rest ->
    if flood_eq entry.fe_ip ip then Some entry else lookup_flood_entry rest ip

(** val update_flood_table :
    floodTable -> iPv4Address -> n -> floodTable*bool **)

let update_flood_table table ip current_time =
  match lookup_flood_entry table ip with
  | Some entry ->
    let time_diff =
      if N.ltb current_time entry.fe_last_request
      then N0
      else N.sub current_time entry.fe_last_request
    in
    if N.leb time_diff aRP_FLOOD_WINDOW
    then let new_count = N.add entry.fe_request_count (Npos XH) in
         if N.leb new_count aRP_FLOOD_THRESHOLD
         then let updated = { fe_ip = ip; fe_last_request = current_time;
                fe_request_count = new_count }
              in
              let replace =
                let rec replace = function
                | [] -> updated::[]
                | e::rest ->
                  if flood_eq e.fe_ip ip
                  then updated::rest
                  else e::(replace rest)
                in replace
              in
              (replace table),true
         else table,false
    else let reset_entry = { fe_ip = ip; fe_last_request = current_time;
           fe_request_count = (Npos XH) }
         in
         let replace =
           let rec replace = function
           | [] -> reset_entry::[]
           | e::rest ->
             if flood_eq e.fe_ip ip
             then reset_entry::rest
             else e::(replace rest)
           in replace
         in
         (replace table),true
  | None ->
    let new_entry = { fe_ip = ip; fe_last_request = current_time;
      fe_request_count = (Npos XH) }
    in
    (new_entry::table),true

(** val clean_flood_table : floodTable -> n -> floodTable **)

let clean_flood_table table current_time =
  filter (fun entry ->
    if N.ltb current_time entry.fe_last_request
    then true
    else N.ltb (N.sub current_time entry.fe_last_request)
           (N.mul aRP_FLOOD_WINDOW (Npos (XO (XI (XO XH)))))) table

(** val add_pending_request :
    enhancedARPContext -> iPv4Address -> n -> enhancedARPContext **)

let add_pending_request ctx target_ip current_time =
  match ctx.earp_state_data with
  | StatePending reqs ->
    let new_req = { preq_target_ip = target_ip; preq_retries = N0;
      preq_timer = (start_timer aRP_REQUEST_TIMEOUT current_time) }
    in
    { earp_my_mac = ctx.earp_my_mac; earp_my_ip = ctx.earp_my_ip;
    earp_cache = ctx.earp_cache; earp_cache_ttl = ctx.earp_cache_ttl;
    earp_state_data = (StatePending (new_req::reqs)); earp_iface =
    ctx.earp_iface; earp_flood_table = ctx.earp_flood_table;
    earp_last_cache_cleanup = ctx.earp_last_cache_cleanup }
  | _ ->
    let new_req = { preq_target_ip = target_ip; preq_retries = N0;
      preq_timer = (start_timer aRP_REQUEST_TIMEOUT current_time) }
    in
    { earp_my_mac = ctx.earp_my_mac; earp_my_ip = ctx.earp_my_ip;
    earp_cache = ctx.earp_cache; earp_cache_ttl = ctx.earp_cache_ttl;
    earp_state_data = (StatePending (new_req::[])); earp_iface =
    ctx.earp_iface; earp_flood_table = ctx.earp_flood_table;
    earp_last_cache_cleanup = ctx.earp_last_cache_cleanup }

(** val remove_pending_request :
    pendingRequest list -> iPv4Address -> pendingRequest list **)

let remove_pending_request reqs target_ip =
  filter (fun req -> negb (ip_eq req.preq_target_ip target_ip)) reqs

(** val retry_pending_request : pendingRequest -> n -> pendingRequest **)

let retry_pending_request req current_time =
  { preq_target_ip = req.preq_target_ip; preq_retries =
    (N.add req.preq_retries (Npos XH)); preq_timer =
    (start_timer aRP_REQUEST_TIMEOUT current_time) }

(** val process_timeouts :
    enhancedARPContext -> n -> enhancedARPContext*aRPEthernetIPv4 list **)

let process_timeouts ctx current_time =
  match ctx.earp_state_data with
  | StatePending reqs ->
    let process_req = fun acc req ->
      let kept_reqs,packets = acc in
      if timer_expired req.preq_timer current_time
      then if N.ltb req.preq_retries aRP_MAX_RETRIES
           then let new_req = retry_pending_request req current_time in
                let arp_req =
                  make_arp_request ctx.earp_my_mac ctx.earp_my_ip
                    req.preq_target_ip
                in
                (new_req::kept_reqs),(arp_req::packets)
           else kept_reqs,packets
      else (req::kept_reqs),packets
    in
    let acc_reqs,packets = fold_left process_req reqs ([],[]) in
    let new_reqs = rev acc_reqs in
    { earp_my_mac = ctx.earp_my_mac; earp_my_ip = ctx.earp_my_ip;
    earp_cache = ctx.earp_cache; earp_cache_ttl = ctx.earp_cache_ttl;
    earp_state_data =
    (match new_reqs with
     | [] -> StateIdle
     | _::_ -> StatePending new_reqs); earp_iface = ctx.earp_iface;
    earp_flood_table = ctx.earp_flood_table; earp_last_cache_cleanup =
    ctx.earp_last_cache_cleanup },(rev packets)
  | _ -> ctx,[]

(** val resolve_address :
    enhancedARPContext -> iPv4Address -> n -> (mACAddress
    option*enhancedARPContext)*aRPEthernetIPv4 option **)

let resolve_address ctx target_ip current_time =
  match lookup_cache ctx.earp_cache target_ip with
  | Some mac -> ((Some mac),ctx),None
  | None ->
    let new_flood,allowed =
      update_flood_table ctx.earp_flood_table target_ip current_time
    in
    if allowed
    then let ctx' = add_pending_request ctx target_ip current_time in
         let ctx'' = { earp_my_mac = ctx'.earp_my_mac; earp_my_ip =
           ctx'.earp_my_ip; earp_cache = ctx'.earp_cache; earp_cache_ttl =
           ctx'.earp_cache_ttl; earp_state_data = ctx'.earp_state_data;
           earp_iface = ctx'.earp_iface; earp_flood_table = new_flood;
           earp_last_cache_cleanup = ctx'.earp_last_cache_cleanup }
         in
         let req = make_arp_request ctx.earp_my_mac ctx.earp_my_ip target_ip
         in
         (None,ctx''),(Some req)
    else (None,ctx),None

(** val start_dad_probe :
    enhancedARPContext -> iPv4Address -> n -> enhancedARPContext **)

let start_dad_probe ctx ip_to_probe current_time =
  { earp_my_mac = ctx.earp_my_mac; earp_my_ip = ctx.earp_my_ip; earp_cache =
    ctx.earp_cache; earp_cache_ttl = ctx.earp_cache_ttl; earp_state_data =
    (StateProbe { probe_ip = ip_to_probe; probe_count = N0; probe_timer =
    (start_timer aRP_PROBE_WAIT current_time) }); earp_iface =
    ctx.earp_iface; earp_flood_table = ctx.earp_flood_table;
    earp_last_cache_cleanup = ctx.earp_last_cache_cleanup }

(** val make_arp_probe : mACAddress -> iPv4Address -> aRPEthernetIPv4 **)

let make_arp_probe my_mac target_ip =
  { arp_op = aRP_OP_REQUEST; arp_sha = my_mac; arp_spa = { ipv4_a = N0;
    ipv4_b = N0; ipv4_c = N0; ipv4_d = N0 }; arp_tha = mAC_ZERO; arp_tpa =
    target_ip }

(** val process_probe_timeout :
    enhancedARPContext -> probeState -> n ->
    enhancedARPContext*aRPEthernetIPv4 option **)

let process_probe_timeout ctx probe current_time =
  if timer_expired probe.probe_timer current_time
  then if N.ltb probe.probe_count aRP_PROBE_NUM
       then let new_probe = { probe_ip = probe.probe_ip; probe_count =
              (N.add probe.probe_count (Npos XH)); probe_timer =
              (start_timer aRP_PROBE_MIN current_time) }
            in
            let ctx' = { earp_my_mac = ctx.earp_my_mac; earp_my_ip =
              ctx.earp_my_ip; earp_cache = ctx.earp_cache; earp_cache_ttl =
              ctx.earp_cache_ttl; earp_state_data = (StateProbe new_probe);
              earp_iface = ctx.earp_iface; earp_flood_table =
              ctx.earp_flood_table; earp_last_cache_cleanup =
              ctx.earp_last_cache_cleanup }
            in
            ctx',(Some (make_arp_probe ctx.earp_my_mac probe.probe_ip))
       else let announce = { announce_count = N0; announce_timer =
              (start_timer aRP_ANNOUNCE_WAIT current_time) }
            in
            let ctx' = { earp_my_mac = ctx.earp_my_mac; earp_my_ip =
              probe.probe_ip; earp_cache = ctx.earp_cache; earp_cache_ttl =
              ctx.earp_cache_ttl; earp_state_data = (StateAnnounce announce);
              earp_iface = ctx.earp_iface; earp_flood_table =
              ctx.earp_flood_table; earp_last_cache_cleanup =
              ctx.earp_last_cache_cleanup }
            in
            ctx',None
  else ctx,None

(** val detect_probe_conflict :
    enhancedARPContext -> probeState -> aRPEthernetIPv4 -> bool **)

let detect_probe_conflict _ probe packet =
  if ip_eq packet.arp_spa probe.probe_ip
  then true
  else ip_eq packet.arp_tpa probe.probe_ip

(** val process_announce_timeout :
    enhancedARPContext -> announceState -> n ->
    enhancedARPContext*aRPEthernetIPv4 option **)

let process_announce_timeout ctx announce current_time =
  if timer_expired announce.announce_timer current_time
  then if N.ltb announce.announce_count aRP_ANNOUNCE_NUM
       then let new_announce = { announce_count =
              (N.add announce.announce_count (Npos XH)); announce_timer =
              (start_timer aRP_ANNOUNCE_INTERVAL current_time) }
            in
            let ctx' = { earp_my_mac = ctx.earp_my_mac; earp_my_ip =
              ctx.earp_my_ip; earp_cache = ctx.earp_cache; earp_cache_ttl =
              ctx.earp_cache_ttl; earp_state_data = (StateAnnounce
              new_announce); earp_iface = ctx.earp_iface; earp_flood_table =
              ctx.earp_flood_table; earp_last_cache_cleanup =
              ctx.earp_last_cache_cleanup }
            in
            ctx',(Some (make_gratuitous_arp ctx.earp_my_mac ctx.earp_my_ip))
       else let ctx' = { earp_my_mac = ctx.earp_my_mac; earp_my_ip =
              ctx.earp_my_ip; earp_cache = ctx.earp_cache; earp_cache_ttl =
              ctx.earp_cache_ttl; earp_state_data = StateIdle; earp_iface =
              ctx.earp_iface; earp_flood_table = ctx.earp_flood_table;
              earp_last_cache_cleanup = ctx.earp_last_cache_cleanup }
            in
            ctx',None
  else ctx,None

(** val detect_address_conflict :
    enhancedARPContext -> aRPEthernetIPv4 -> bool **)

let detect_address_conflict ctx packet =
  if ip_eq packet.arp_spa ctx.earp_my_ip
  then (match list_eq_dec N.eq_dec packet.arp_sha ctx.earp_my_mac with
        | Left -> false
        | Right -> true)
  else false

(** val can_defend : defendState -> n -> bool **)

let can_defend defend current_time =
  N.leb (N.add defend aRP_DEFEND_INTERVAL) current_time

(** val make_defend_packet : enhancedARPContext -> aRPEthernetIPv4 **)

let make_defend_packet ctx =
  make_gratuitous_arp ctx.earp_my_mac ctx.earp_my_ip

(** val process_conflict :
    enhancedARPContext -> n -> enhancedARPContext*aRPEthernetIPv4 option **)

let process_conflict ctx current_time =
  match ctx.earp_state_data with
  | StateDefend defend ->
    if can_defend defend current_time
    then let ctx' = { earp_my_mac = ctx.earp_my_mac; earp_my_ip =
           ctx.earp_my_ip; earp_cache = ctx.earp_cache; earp_cache_ttl =
           ctx.earp_cache_ttl; earp_state_data = (StateDefend current_time);
           earp_iface = ctx.earp_iface; earp_flood_table =
           ctx.earp_flood_table; earp_last_cache_cleanup =
           ctx.earp_last_cache_cleanup }
         in
         ctx',(Some (make_defend_packet ctx))
    else ctx,None
  | StateConflict (_, conflict_timer) ->
    if timer_expired conflict_timer current_time
    then let ctx' = { earp_my_mac = ctx.earp_my_mac; earp_my_ip =
           ctx.earp_my_ip; earp_cache = ctx.earp_cache; earp_cache_ttl =
           ctx.earp_cache_ttl; earp_state_data = StateIdle; earp_iface =
           ctx.earp_iface; earp_flood_table = ctx.earp_flood_table;
           earp_last_cache_cleanup = ctx.earp_last_cache_cleanup }
         in
         ctx',None
    else ctx,None
  | _ ->
    let ctx' = { earp_my_mac = ctx.earp_my_mac; earp_my_ip = ctx.earp_my_ip;
      earp_cache = ctx.earp_cache; earp_cache_ttl = ctx.earp_cache_ttl;
      earp_state_data = (StateDefend current_time); earp_iface =
      ctx.earp_iface; earp_flood_table = ctx.earp_flood_table;
      earp_last_cache_cleanup = ctx.earp_last_cache_cleanup }
    in
    ctx',(Some (make_defend_packet ctx))

(** val send_arp_request_with_flood_check :
    enhancedARPContext -> iPv4Address -> n ->
    enhancedARPContext*aRPEthernetIPv4 option **)

let send_arp_request_with_flood_check ctx target_ip current_time =
  let new_flood_table,allowed =
    update_flood_table ctx.earp_flood_table target_ip current_time
  in
  if allowed
  then let ctx' = { earp_my_mac = ctx.earp_my_mac; earp_my_ip =
         ctx.earp_my_ip; earp_cache = ctx.earp_cache; earp_cache_ttl =
         ctx.earp_cache_ttl; earp_state_data = ctx.earp_state_data;
         earp_iface = ctx.earp_iface; earp_flood_table = new_flood_table;
         earp_last_cache_cleanup = ctx.earp_last_cache_cleanup }
       in
       let request = make_arp_request ctx.earp_my_mac ctx.earp_my_ip target_ip
       in
       ctx',(Some request)
  else let ctx' = { earp_my_mac = ctx.earp_my_mac; earp_my_ip =
         ctx.earp_my_ip; earp_cache = ctx.earp_cache; earp_cache_ttl =
         ctx.earp_cache_ttl; earp_state_data = ctx.earp_state_data;
         earp_iface = ctx.earp_iface; earp_flood_table = new_flood_table;
         earp_last_cache_cleanup = ctx.earp_last_cache_cleanup }
       in
       ctx',None

(** val age_cache : aRPCache -> n -> aRPCache **)

let age_cache cache elapsed =
  let dec = fun e ->
    if e.ace_static
    then e
    else { ace_ip = e.ace_ip; ace_mac = e.ace_mac; ace_ttl =
           (N.sub e.ace_ttl elapsed); ace_static = e.ace_static }
  in
  filter (fun e -> if e.ace_static then true else negb (N.leb e.ace_ttl N0))
    (map dec cache)

(** val age_all_interface_caches :
    multiInterfaceARPContext -> n -> multiInterfaceARPContext **)

let age_all_interface_caches ctx elapsed =
  let age_all =
    map (fun iface ->
      update_interface_cache iface (age_cache iface.ifex_cache elapsed))
      ctx.mi_interfaces
  in
  { mi_interfaces = age_all; mi_global_flood_table =
  ctx.mi_global_flood_table; mi_last_cleanup =
  (N.add ctx.mi_last_cleanup elapsed) }

(** val process_arp_packet_enhanced :
    enhancedARPContext -> aRPEthernetIPv4 -> n -> n ->
    enhancedARPContext*aRPEthernetIPv4 option **)

let process_arp_packet_enhanced ctx packet current_time elapsed_since_last =
  let aged_cache = age_cache ctx.earp_cache elapsed_since_last in
  let cleaned_flood = clean_flood_table ctx.earp_flood_table current_time in
  let ctx_aged = { earp_my_mac = ctx.earp_my_mac; earp_my_ip =
    ctx.earp_my_ip; earp_cache = aged_cache; earp_cache_ttl =
    ctx.earp_cache_ttl; earp_state_data = ctx.earp_state_data; earp_iface =
    ctx.earp_iface; earp_flood_table = cleaned_flood;
    earp_last_cache_cleanup = current_time }
  in
  if is_broadcast_mac packet.arp_sha
  then ctx_aged,None
  else if is_suspicious_arp ctx_aged.earp_cache packet
       then ctx_aged,None
       else (match ctx_aged.earp_state_data with
             | StateProbe probe ->
               if detect_probe_conflict ctx_aged probe packet
               then let conflict_timer =
                      start_timer aRP_CONFLICT_RECOVERY_WAIT current_time
                    in
                    let ctx' = { earp_my_mac = ctx_aged.earp_my_mac;
                      earp_my_ip = ctx_aged.earp_my_ip; earp_cache =
                      ctx_aged.earp_cache; earp_cache_ttl =
                      ctx_aged.earp_cache_ttl; earp_state_data =
                      (StateConflict (probe.probe_ip, conflict_timer));
                      earp_iface = ctx_aged.earp_iface; earp_flood_table =
                      ctx_aged.earp_flood_table; earp_last_cache_cleanup =
                      ctx_aged.earp_last_cache_cleanup }
                    in
                    ctx',None
               else let i_am_target = ip_eq packet.arp_tpa ctx_aged.earp_my_ip
                    in
                    let cache' =
                      rfc826_merge ctx_aged.earp_cache packet.arp_spa
                        packet.arp_sha ctx_aged.earp_cache_ttl i_am_target
                    in
                    let ctx' = { earp_my_mac = ctx_aged.earp_my_mac;
                      earp_my_ip = ctx_aged.earp_my_ip; earp_cache = cache';
                      earp_cache_ttl = ctx_aged.earp_cache_ttl;
                      earp_state_data = ctx_aged.earp_state_data;
                      earp_iface = ctx_aged.earp_iface; earp_flood_table =
                      ctx_aged.earp_flood_table; earp_last_cache_cleanup =
                      ctx_aged.earp_last_cache_cleanup }
                    in
                    ctx',None
             | _ ->
               if detect_address_conflict ctx_aged packet
               then process_conflict ctx_aged current_time
               else let i_am_target = ip_eq packet.arp_tpa ctx_aged.earp_my_ip
                    in
                    let cache' =
                      rfc826_merge ctx_aged.earp_cache packet.arp_spa
                        packet.arp_sha ctx_aged.earp_cache_ttl i_am_target
                    in
                    let new_state =
                      match ctx_aged.earp_state_data with
                      | StatePending reqs ->
                        if N.eqb packet.arp_op aRP_OP_REPLY
                        then StatePending
                               (remove_pending_request reqs packet.arp_spa)
                        else StatePending reqs
                      | x -> x
                    in
                    let ctx' = { earp_my_mac = ctx_aged.earp_my_mac;
                      earp_my_ip = ctx_aged.earp_my_ip; earp_cache = cache';
                      earp_cache_ttl = ctx_aged.earp_cache_ttl;
                      earp_state_data = new_state; earp_iface =
                      ctx_aged.earp_iface; earp_flood_table =
                      ctx_aged.earp_flood_table; earp_last_cache_cleanup =
                      ctx_aged.earp_last_cache_cleanup }
                    in
                    if ip_eq packet.arp_tpa ctx_aged.earp_my_ip
                    then if N.eqb packet.arp_op aRP_OP_REQUEST
                         then let reply =
                                make_arp_reply ctx_aged.earp_my_mac
                                  ctx_aged.earp_my_ip packet.arp_sha
                                  packet.arp_spa
                              in
                              ctx',(Some reply)
                         else ctx',None
                    else ctx',None)

(** val send_arp_on_interface :
    networkInterface -> aRPEthernetIPv4 -> bool **)

let send_arp_on_interface iface _ =
  iface.if_up

type networkEvent =
| SendPacket of aRPPacket
| ReceivePacket of aRPPacket
| Timeout of n

type networkNode = { node_ctx : aRPContext; node_time : n }

(** val process_event : networkNode -> networkEvent -> networkNode **)

let process_event node = function
| SendPacket _ -> node
| ReceivePacket pkt ->
  (match process_generic_arp pkt with
   | Some arp_pkt ->
     let ctx',_ = process_arp_packet node.node_ctx arp_pkt in
     { node_ctx = ctx'; node_time = node.node_time }
   | None -> node)
| Timeout elapsed ->
  let aged_cache = age_cache node.node_ctx.arp_cache elapsed in
  { node_ctx = { arp_my_mac = node.node_ctx.arp_my_mac; arp_my_ip =
  node.node_ctx.arp_my_ip; arp_cache = aged_cache; arp_cache_ttl =
  node.node_ctx.arp_cache_ttl }; node_time = (N.add node.node_time elapsed) }

type enhancedEvent =
| EPacketIn of aRPEthernetIPv4
| ETimerTick of n
| EProbeTimeout
| EAnnounceTimeout
| ERequestTimeout

type enhancedNode = { enode_ctx : enhancedARPContext; enode_time : n }

(** val enhanced_process_event :
    enhancedNode -> enhancedEvent -> enhancedNode*aRPEthernetIPv4 list **)

let enhanced_process_event node event =
  let current_time = node.enode_time in
  (match event with
   | EPacketIn packet ->
     let elapsed = N0 in
     let ctx',resp =
       process_arp_packet_enhanced node.enode_ctx packet current_time elapsed
     in
     let outgoing = match resp with
                    | Some pkt -> pkt::[]
                    | None -> [] in
     { enode_ctx = ctx'; enode_time = current_time },outgoing
   | ETimerTick elapsed ->
     let ctx',outgoing =
       process_timeouts node.enode_ctx (N.add current_time elapsed)
     in
     { enode_ctx = ctx'; enode_time = (N.add current_time elapsed) },outgoing
   | EProbeTimeout ->
     (match node.enode_ctx.earp_state_data with
      | StateProbe probe ->
        let ctx',pkt_opt =
          process_probe_timeout node.enode_ctx probe current_time
        in
        let outgoing = match pkt_opt with
                       | Some pkt -> pkt::[]
                       | None -> [] in
        { enode_ctx = ctx'; enode_time = current_time },outgoing
      | _ -> node,[])
   | EAnnounceTimeout ->
     (match node.enode_ctx.earp_state_data with
      | StateAnnounce announce ->
        let ctx',pkt_opt =
          process_announce_timeout node.enode_ctx announce current_time
        in
        let outgoing = match pkt_opt with
                       | Some pkt -> pkt::[]
                       | None -> [] in
        { enode_ctx = ctx'; enode_time = current_time },outgoing
      | _ -> node,[])
   | ERequestTimeout ->
     let ctx',outgoing = process_timeouts node.enode_ctx current_time in
     { enode_ctx = ctx'; enode_time = current_time },outgoing)
