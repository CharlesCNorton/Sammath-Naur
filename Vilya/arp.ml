
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type comparison =
| Eq
| Lt
| Gt

type sumbool =
| Left
| Right

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

(** val eTHERNET_ADDR_LEN : byte **)

let eTHERNET_ADDR_LEN =
  Npos (XO (XI XH))

(** val iPV4_ADDR_LEN : byte **)

let iPV4_ADDR_LEN =
  Npos (XO (XO XH))

type mACAddress =
  byte list
  (* singleton inductive, whose constructor was Build_MACAddress *)

type iPv4Address = { ipv4_a : byte; ipv4_b : byte; ipv4_c : byte;
                     ipv4_d : byte }

(** val mAC_BROADCAST : mACAddress **)

let mAC_BROADCAST =
  (Npos (XI (XI (XI (XI (XI (XI (XI XH))))))))::((Npos (XI (XI (XI (XI (XI
    (XI (XI XH))))))))::((Npos (XI (XI (XI (XI (XI (XI (XI XH))))))))::((Npos
    (XI (XI (XI (XI (XI (XI (XI XH))))))))::((Npos (XI (XI (XI (XI (XI (XI
    (XI XH))))))))::((Npos (XI (XI (XI (XI (XI (XI (XI XH))))))))::[])))))

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

(** val make_arp_request :
    mACAddress -> iPv4Address -> iPv4Address -> aRPEthernetIPv4 **)

let make_arp_request my_mac my_ip target_ip =
  { arp_op = aRP_OP_REQUEST; arp_sha = my_mac; arp_spa = my_ip; arp_tha =
    mAC_BROADCAST; arp_tpa = target_ip }

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

type aRPState =
| ARP_IDLE
| ARP_PROBE
| ARP_ANNOUNCE
| ARP_DEFEND

type aRPContext = { arp_my_mac : mACAddress; arp_my_ip : iPv4Address;
                    arp_cache : aRPCache; arp_state : aRPState;
                    arp_pending : iPv4Address list; arp_retries : n }

(** val process_arp_packet :
    aRPContext -> aRPEthernetIPv4 -> aRPContext*aRPEthernetIPv4 option **)

let process_arp_packet ctx packet =
  if is_broadcast_mac packet.arp_sha
  then ctx,None
  else let i_am_target = ip_eq packet.arp_tpa ctx.arp_my_ip in
       let cache' =
         rfc826_merge ctx.arp_cache packet.arp_spa packet.arp_sha (Npos (XO
           (XO (XI (XI (XO (XI (XO (XO XH))))))))) i_am_target
       in
       let ctx' = { arp_my_mac = ctx.arp_my_mac; arp_my_ip = ctx.arp_my_ip;
         arp_cache = cache'; arp_state = ctx.arp_state; arp_pending =
         ctx.arp_pending; arp_retries = ctx.arp_retries }
       in
       if i_am_target
       then if N.eqb packet.arp_op aRP_OP_REQUEST
            then let reply =
                   make_arp_reply ctx.arp_my_mac ctx.arp_my_ip packet.arp_sha
                     packet.arp_spa
                 in
                 ctx',(Some reply)
            else ctx',None
       else ctx',None

(** val make_gratuitous_arp : mACAddress -> iPv4Address -> aRPEthernetIPv4 **)

let make_gratuitous_arp my_mac my_ip =
  { arp_op = aRP_OP_REQUEST; arp_sha = my_mac; arp_spa = my_ip; arp_tha =
    mAC_BROADCAST; arp_tpa = my_ip }

(** val aRP_REQUEST_TIMEOUT : n **)

let aRP_REQUEST_TIMEOUT =
  Npos (XO (XO (XO (XI (XO (XI (XI (XI (XI XH)))))))))

(** val aRP_MAX_RETRIES : n **)

let aRP_MAX_RETRIES =
  Npos (XI XH)

(** val aRP_PROBE_WAIT : n **)

let aRP_PROBE_WAIT =
  Npos (XO (XO (XO (XI (XO (XI (XI (XI (XI XH)))))))))

(** val aRP_DEFEND_INTERVAL : n **)

let aRP_DEFEND_INTERVAL =
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

type networkInterface = { if_mac : mACAddress; if_ip : iPv4Address;
                          if_mtu : n; if_up : bool }

type floodEntry = { fe_ip : iPv4Address; fe_last_request : n;
                    fe_request_count : n }

type floodTable = floodEntry list

type enhancedARPContext = { earp_my_mac : mACAddress;
                            earp_my_ip : iPv4Address; earp_cache : aRPCache;
                            earp_state_data : aRPStateData;
                            earp_iface : networkInterface;
                            earp_flood_table : floodTable;
                            earp_last_cache_cleanup : n }

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
    let time_diff = N.sub current_time entry.fe_last_request in
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
    N.ltb (N.sub current_time entry.fe_last_request)
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
    earp_cache = ctx.earp_cache; earp_state_data = (StatePending
    (new_req::reqs)); earp_iface = ctx.earp_iface; earp_flood_table =
    ctx.earp_flood_table; earp_last_cache_cleanup =
    ctx.earp_last_cache_cleanup }
  | _ ->
    let new_req = { preq_target_ip = target_ip; preq_retries = N0;
      preq_timer = (start_timer aRP_REQUEST_TIMEOUT current_time) }
    in
    { earp_my_mac = ctx.earp_my_mac; earp_my_ip = ctx.earp_my_ip;
    earp_cache = ctx.earp_cache; earp_state_data = (StatePending
    (new_req::[])); earp_iface = ctx.earp_iface; earp_flood_table =
    ctx.earp_flood_table; earp_last_cache_cleanup =
    ctx.earp_last_cache_cleanup }

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
    let new_reqs,packets = fold_left process_req reqs ([],[]) in
    { earp_my_mac = ctx.earp_my_mac; earp_my_ip = ctx.earp_my_ip;
    earp_cache = ctx.earp_cache; earp_state_data =
    (match new_reqs with
     | [] -> StatePending new_reqs
     | _::_ -> StateIdle); earp_iface = ctx.earp_iface; earp_flood_table =
    ctx.earp_flood_table; earp_last_cache_cleanup =
    ctx.earp_last_cache_cleanup },packets
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
           ctx'.earp_my_ip; earp_cache = ctx'.earp_cache; earp_state_data =
           ctx'.earp_state_data; earp_iface = ctx'.earp_iface;
           earp_flood_table = new_flood; earp_last_cache_cleanup =
           ctx'.earp_last_cache_cleanup }
         in
         let req = make_arp_request ctx.earp_my_mac ctx.earp_my_ip target_ip
         in
         (None,ctx''),(Some req)
    else (None,ctx),None

(** val start_dad_probe :
    enhancedARPContext -> iPv4Address -> n -> enhancedARPContext **)

let start_dad_probe ctx ip_to_probe current_time =
  { earp_my_mac = ctx.earp_my_mac; earp_my_ip = ctx.earp_my_ip; earp_cache =
    ctx.earp_cache; earp_state_data = (StateProbe { probe_ip = ip_to_probe;
    probe_count = N0; probe_timer =
    (start_timer aRP_PROBE_WAIT current_time) }); earp_iface =
    ctx.earp_iface; earp_flood_table = ctx.earp_flood_table;
    earp_last_cache_cleanup = ctx.earp_last_cache_cleanup }

(** val make_arp_probe : mACAddress -> iPv4Address -> aRPEthernetIPv4 **)

let make_arp_probe my_mac target_ip =
  { arp_op = aRP_OP_REQUEST; arp_sha = my_mac; arp_spa = { ipv4_a = N0;
    ipv4_b = N0; ipv4_c = N0; ipv4_d = N0 }; arp_tha = mAC_BROADCAST;
    arp_tpa = target_ip }

(** val detect_probe_conflict :
    enhancedARPContext -> probeState -> aRPEthernetIPv4 -> bool **)

let detect_probe_conflict _ probe packet =
  if ip_eq packet.arp_spa probe.probe_ip
  then true
  else ip_eq packet.arp_tpa probe.probe_ip

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
           ctx.earp_my_ip; earp_cache = ctx.earp_cache; earp_state_data =
           (StateDefend current_time); earp_iface = ctx.earp_iface;
           earp_flood_table = ctx.earp_flood_table; earp_last_cache_cleanup =
           ctx.earp_last_cache_cleanup }
         in
         ctx',(Some (make_defend_packet ctx))
    else ctx,None
  | _ ->
    let ctx' = { earp_my_mac = ctx.earp_my_mac; earp_my_ip = ctx.earp_my_ip;
      earp_cache = ctx.earp_cache; earp_state_data = (StateDefend
      current_time); earp_iface = ctx.earp_iface; earp_flood_table =
      ctx.earp_flood_table; earp_last_cache_cleanup =
      ctx.earp_last_cache_cleanup }
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
         ctx.earp_my_ip; earp_cache = ctx.earp_cache; earp_state_data =
         ctx.earp_state_data; earp_iface = ctx.earp_iface; earp_flood_table =
         new_flood_table; earp_last_cache_cleanup =
         ctx.earp_last_cache_cleanup }
       in
       let request = make_arp_request ctx.earp_my_mac ctx.earp_my_ip target_ip
       in
       ctx',(Some request)
  else let ctx' = { earp_my_mac = ctx.earp_my_mac; earp_my_ip =
         ctx.earp_my_ip; earp_cache = ctx.earp_cache; earp_state_data =
         ctx.earp_state_data; earp_iface = ctx.earp_iface; earp_flood_table =
         new_flood_table; earp_last_cache_cleanup =
         ctx.earp_last_cache_cleanup }
       in
       ctx',None

(** val age_cache : aRPCache -> n -> aRPCache **)

let age_cache cache elapsed =
  filter (fun entry ->
    if entry.ace_static then true else negb (N.leb entry.ace_ttl elapsed))
    (map (fun entry ->
      if entry.ace_static
      then entry
      else { ace_ip = entry.ace_ip; ace_mac = entry.ace_mac; ace_ttl =
             (N.sub entry.ace_ttl elapsed); ace_static = entry.ace_static })
      cache)

(** val process_arp_packet_enhanced :
    enhancedARPContext -> aRPEthernetIPv4 -> n -> n ->
    enhancedARPContext*aRPEthernetIPv4 option **)

let process_arp_packet_enhanced ctx packet current_time elapsed_since_last =
  let aged_cache = age_cache ctx.earp_cache elapsed_since_last in
  let cleaned_flood = clean_flood_table ctx.earp_flood_table current_time in
  let ctx_aged = { earp_my_mac = ctx.earp_my_mac; earp_my_ip =
    ctx.earp_my_ip; earp_cache = aged_cache; earp_state_data =
    ctx.earp_state_data; earp_iface = ctx.earp_iface; earp_flood_table =
    cleaned_flood; earp_last_cache_cleanup = current_time }
  in
  (match ctx_aged.earp_state_data with
   | StateProbe probe ->
     if detect_probe_conflict ctx_aged probe packet
     then let ctx' = start_dad_probe ctx_aged probe.probe_ip current_time in
          ctx',None
     else let cache' =
            merge_cache_entry ctx_aged.earp_cache packet.arp_spa
              packet.arp_sha (Npos (XO (XO (XI (XI (XO (XI (XO (XO XH)))))))))
          in
          let ctx' = { earp_my_mac = ctx_aged.earp_my_mac; earp_my_ip =
            ctx_aged.earp_my_ip; earp_cache = cache'; earp_state_data =
            ctx_aged.earp_state_data; earp_iface = ctx_aged.earp_iface;
            earp_flood_table = ctx_aged.earp_flood_table;
            earp_last_cache_cleanup = ctx_aged.earp_last_cache_cleanup }
          in
          ctx',None
   | _ ->
     if detect_address_conflict ctx_aged packet
     then process_conflict ctx_aged current_time
     else let cache' =
            merge_cache_entry ctx_aged.earp_cache packet.arp_spa
              packet.arp_sha (Npos (XO (XO (XI (XI (XO (XI (XO (XO XH)))))))))
          in
          let new_state =
            match ctx_aged.earp_state_data with
            | StatePending reqs ->
              if N.eqb packet.arp_op aRP_OP_REPLY
              then StatePending (remove_pending_request reqs packet.arp_spa)
              else StatePending reqs
            | x -> x
          in
          let ctx' = { earp_my_mac = ctx_aged.earp_my_mac; earp_my_ip =
            ctx_aged.earp_my_ip; earp_cache = cache'; earp_state_data =
            new_state; earp_iface = ctx_aged.earp_iface; earp_flood_table =
            ctx_aged.earp_flood_table; earp_last_cache_cleanup =
            ctx_aged.earp_last_cache_cleanup }
          in
          if ip_eq packet.arp_tpa ctx_aged.earp_my_ip
          then if N.eqb packet.arp_op aRP_OP_REQUEST
               then let reply =
                      make_arp_reply ctx_aged.earp_my_mac ctx_aged.earp_my_ip
                        packet.arp_sha packet.arp_spa
                    in
                    ctx',(Some reply)
               else ctx',None
          else ctx',None)
