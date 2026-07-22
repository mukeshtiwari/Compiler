
type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type sumbool =
| Left
| Right

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)

 let rec add n0 m =
   match n0 with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val mul : nat -> nat -> nat **)

let rec mul n0 m =
  match n0 with
  | O -> O
  | S p -> add m (mul p m)

(** val sub : nat -> nat -> nat **)

let rec sub n0 m =
  match n0 with
  | O -> n0
  | S k -> (match m with
            | O -> n0
            | S l -> sub k l)

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
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

  type mask =
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

  (** val div2 : positive -> positive **)

  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH

  (** val div2_up : positive -> positive **)

  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH

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

  (** val ldiff : positive -> positive -> n **)

  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH -> (match q with
             | XO _ -> Npos XH
             | _ -> N0)

  (** val coq_lxor : positive -> positive -> n **)

  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

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

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)

  (** val size : positive -> positive **)

  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH

  (** val testbit : positive -> n -> bool **)

  let rec testbit p n0 =
    match p with
    | XI p0 -> (match n0 with
                | N0 -> True
                | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 -> (match n0 with
                | N0 -> False
                | Npos n1 -> testbit p0 (pred_N n1))
    | XH -> (match n0 with
             | N0 -> True
             | Npos _ -> False)

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
  (** val succ_double : n -> n **)

  let succ_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val double : n -> n **)

  let double = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val succ_pos : n -> positive **)

  let succ_pos = function
  | N0 -> XH
  | Npos p -> Pos.succ p

  (** val sub : n -> n -> n **)

  let sub n0 m =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n0
       | Npos m' ->
         (match Pos.sub_mask n' m' with
          | Pos.IsPos p -> Npos p
          | _ -> N0))

  (** val compare : n -> n -> comparison **)

  let compare n0 m =
    match n0 with
    | N0 -> (match m with
             | N0 -> Eq
             | Npos _ -> Lt)
    | Npos n' -> (match m with
                  | N0 -> Gt
                  | Npos m' -> Pos.compare n' m')

  (** val leb : n -> n -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val pos_div_eucl : positive -> n -> (n, n) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      (match leb b r' with
       | True -> Pair ((succ_double q), (sub r' b))
       | False -> Pair ((double q), r'))
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = double r in
      (match leb b r' with
       | True -> Pair ((succ_double q), (sub r' b))
       | False -> Pair ((double q), r'))
    | XH ->
      (match b with
       | N0 -> Pair (N0, (Npos XH))
       | Npos p ->
         (match p with
          | XH -> Pair ((Npos XH), N0)
          | _ -> Pair (N0, (Npos XH))))

  (** val coq_lor : n -> n -> n **)

  let coq_lor n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Pos.coq_lor p q))

  (** val coq_land : n -> n -> n **)

  let coq_land n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Pos.coq_land p q)

  (** val ldiff : n -> n -> n **)

  let ldiff n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Pos.ldiff p q)

  (** val coq_lxor : n -> n -> n **)

  let coq_lxor n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Pos.coq_lxor p q)
 end

module Coq_N =
 struct
  (** val testbit : n -> n -> bool **)

  let testbit a n0 =
    match a with
    | N0 -> False
    | Npos p -> Coq_Pos.testbit p n0
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n0 =
    add m (opp n0)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> True
    | _ -> False

  (** val to_nat : z -> nat **)

  let to_nat = function
  | Zpos p -> Pos.to_nat p
  | _ -> O

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n1 -> Zpos (Pos.of_succ_nat n1)

  (** val of_N : n -> z **)

  let of_N = function
  | N0 -> Z0
  | Npos p -> Zpos p

  (** val pos_div_eucl : positive -> z -> (z, z) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q), r')
       | False -> Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b)))
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q), r')
       | False -> Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b)))
    | XH ->
      (match leb (Zpos (XO XH)) b with
       | True -> Pair (Z0, (Zpos XH))
       | False -> Pair ((Zpos XH), Z0))

  (** val div_eucl : z -> z -> (z, z) prod **)

  let div_eucl a b =
    match a with
    | Z0 -> Pair (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let Pair (q, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos _ ->
         let Pair (q, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (sub b r)))
       | Zneg b' ->
         let Pair (q, r) = pos_div_eucl a' (Zpos b') in Pair (q, (opp r)))

  (** val div : z -> z -> z **)

  let div a b =
    let Pair (q, _) = div_eucl a b in q

  (** val modulo : z -> z -> z **)

  let modulo a b =
    let Pair (_, r) = div_eucl a b in r

  (** val quotrem : z -> z -> (z, z) prod **)

  let quotrem a b =
    match a with
    | Z0 -> Pair (Z0, Z0)
    | Zpos a0 ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos b0 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Pair ((of_N q), (of_N r))
       | Zneg b0 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Pair ((opp (of_N q)), (of_N r)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos b0 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Pair ((opp (of_N q)), (opp (of_N r)))
       | Zneg b0 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Pair ((of_N q), (opp (of_N r))))

  (** val quot : z -> z -> z **)

  let quot a b =
    fst (quotrem a b)

  (** val rem : z -> z -> z **)

  let rem a b =
    snd (quotrem a b)

  (** val div2 : z -> z **)

  let div2 = function
  | Z0 -> Z0
  | Zpos p -> (match p with
               | XH -> Z0
               | _ -> Zpos (Pos.div2 p))
  | Zneg p -> Zneg (Pos.div2_up p)

  (** val shiftl : z -> z -> z **)

  let shiftl a = function
  | Z0 -> a
  | Zpos p -> Pos.iter (mul (Zpos (XO XH))) a p
  | Zneg p -> Pos.iter div2 a p

  (** val shiftr : z -> z -> z **)

  let shiftr a n0 =
    shiftl a (opp n0)

  (** val coq_lor : z -> z -> z **)

  let coq_lor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zpos (Pos.coq_lor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.ldiff (Pos.pred_N b0) (Npos a0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.ldiff (Pos.pred_N a0) (Npos b0)))
       | Zneg b0 ->
         Zneg (N.succ_pos (N.coq_land (Pos.pred_N a0) (Pos.pred_N b0))))

  (** val coq_land : z -> z -> z **)

  let coq_land a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (Pos.coq_land a0 b0)
       | Zneg b0 -> of_N (N.ldiff (Npos a0) (Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (N.ldiff (Npos b0) (Pos.pred_N a0))
       | Zneg b0 ->
         Zneg (N.succ_pos (N.coq_lor (Pos.pred_N a0) (Pos.pred_N b0))))

  (** val coq_lxor : z -> z -> z **)

  let coq_lxor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Pos.coq_lxor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.coq_lxor (Npos a0) (Pos.pred_N b0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.coq_lxor (Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (N.coq_lxor (Pos.pred_N a0) (Pos.pred_N b0)))

  (** val pred : z -> z **)

  let pred x =
    add x (Zneg XH)

  (** val iter : z -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let iter n0 f x =
    match n0 with
    | Zpos p -> Coq_Pos.iter f x p
    | _ -> x

  (** val odd : z -> bool **)

  let odd = function
  | Z0 -> False
  | Zpos p -> (match p with
               | XO _ -> False
               | _ -> True)
  | Zneg p -> (match p with
               | XO _ -> False
               | _ -> True)

  (** val log2 : z -> z **)

  let log2 = function
  | Zpos p0 ->
    (match p0 with
     | XI p -> Zpos (Coq_Pos.size p)
     | XO p -> Zpos (Coq_Pos.size p)
     | XH -> Z0)
  | _ -> Z0

  (** val testbit : z -> z -> bool **)

  let testbit a = function
  | Z0 -> odd a
  | Zpos p ->
    (match a with
     | Z0 -> False
     | Zpos a0 -> Coq_Pos.testbit a0 (Npos p)
     | Zneg a0 -> negb (Coq_N.testbit (Coq_Pos.pred_N a0) (Npos p)))
  | Zneg _ -> False

  (** val eq_dec : z -> z -> sumbool **)

  let eq_dec x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Left
             | _ -> Right)
    | Zpos p -> (match y with
                 | Zpos p0 -> Coq_Pos.eq_dec p p0
                 | _ -> Right)
    | Zneg p -> (match y with
                 | Zneg p0 -> Coq_Pos.eq_dec p p0
                 | _ -> Right)

  (** val ones : z -> z **)

  let ones n0 =
    pred (shiftl (Zpos XH) n0)
 end

(** val z_lt_dec : z -> z -> sumbool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> Left
  | _ -> Right

(** val z_le_dec : z -> z -> sumbool **)

let z_le_dec x y =
  match Z.compare x y with
  | Gt -> Right
  | _ -> Left

(** val z_le_gt_dec : z -> z -> sumbool **)

let z_le_gt_dec =
  z_le_dec

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, l0) -> Cons ((f a), (map f l0))

(** val seq : nat -> nat -> nat list **)

let rec seq start = function
| O -> Nil
| S len0 -> Cons (start, (seq (S start) len0))

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| Nil -> a0
| Cons (b, l0) -> f b (fold_right f a0 l0)

(** val shift_nat : nat -> positive -> positive **)

let rec shift_nat n0 z0 =
  match n0 with
  | O -> z0
  | S n1 -> XO (shift_nat n1 z0)

(** val shift_pos : positive -> positive -> positive **)

let shift_pos n0 z0 =
  Coq_Pos.iter (fun x -> XO x) z0 n0

(** val two_power_nat : nat -> z **)

let two_power_nat n0 =
  Zpos (shift_nat n0 XH)

(** val two_power_pos : positive -> z **)

let two_power_pos x =
  Zpos (shift_pos x XH)

(** val two_p : z -> z **)

let two_p = function
| Z0 -> Zpos XH
| Zpos y -> two_power_pos y
| Zneg _ -> Z0

module Byte =
 struct
  type t = z
    (* singleton inductive, whose constructor was Build_t *)

  (** val unsigned : t -> z **)

  let unsigned t0 =
    t0
 end

(** val byte_nat : Byte.t -> nat **)

let byte_nat =
  Z.to_nat

type opcode =
| OpStop
| OpLoad of nat
| OpStore of nat
| OpPop
| OpAdd
| OpSub
| OpDup
| OpJumpdest
| OpJumpi

(** val opcode_width : opcode -> nat **)

let opcode_width = function
| OpLoad _ -> S (S O)
| OpStore _ -> S (S O)
| _ -> S O

type instruction = { instr_pc : nat; instr_opcode : opcode; instr_next : nat }

(** val make_instruction : nat -> opcode -> instruction **)

let make_instruction pc op =
  { instr_pc = pc; instr_opcode = op; instr_next =
    (add pc (opcode_width op)) }

type parse_error =
| UnknownOpcode of nat * nat
| TruncatedOperand of nat

type 'a parse_result =
| Parsed of 'a
| Rejected of parse_error

(** val prepend_instruction :
    instruction -> instruction list parse_result -> instruction list
    parse_result **)

let prepend_instruction i = function
| Parsed code0 -> Parsed (Cons (i, code0))
| Rejected error -> Rejected error

type operand_kind =
| LoadOperand
| StoreOperand

type scan_mode =
| ExpectOpcode of nat
| ExpectOperand of nat * operand_kind

(** val scan : scan_mode -> Byte.t list -> instruction list parse_result **)

let rec scan mode bytes =
  match mode with
  | ExpectOpcode pc ->
    (match bytes with
     | Nil -> Parsed Nil
     | Cons (opbyte, tail) ->
       (match byte_nat opbyte with
        | O ->
          prepend_instruction (make_instruction pc OpStop)
            (scan (ExpectOpcode (S pc)) tail)
        | S n0 ->
          (match n0 with
           | O -> scan (ExpectOperand (pc, LoadOperand)) tail
           | S n1 ->
             (match n1 with
              | O -> scan (ExpectOperand (pc, StoreOperand)) tail
              | S n2 ->
                (match n2 with
                 | O ->
                   prepend_instruction (make_instruction pc OpPop)
                     (scan (ExpectOpcode (S pc)) tail)
                 | S n3 ->
                   (match n3 with
                    | O ->
                      prepend_instruction (make_instruction pc OpAdd)
                        (scan (ExpectOpcode (S pc)) tail)
                    | S n4 ->
                      (match n4 with
                       | O ->
                         prepend_instruction (make_instruction pc OpSub)
                           (scan (ExpectOpcode (S pc)) tail)
                       | S n5 ->
                         (match n5 with
                          | O ->
                            prepend_instruction (make_instruction pc OpDup)
                              (scan (ExpectOpcode (S pc)) tail)
                          | S n6 ->
                            (match n6 with
                             | O ->
                               prepend_instruction
                                 (make_instruction pc OpJumpdest)
                                 (scan (ExpectOpcode (S pc)) tail)
                             | S n7 ->
                               (match n7 with
                                | O ->
                                  prepend_instruction
                                    (make_instruction pc OpJumpi)
                                    (scan (ExpectOpcode (S pc)) tail)
                                | S n8 ->
                                  Rejected (UnknownOpcode (pc, (S (S (S (S (S
                                    (S (S (S (S n8)))))))))))))))))))))
  | ExpectOperand (pc, kind) ->
    (match kind with
     | LoadOperand ->
       (match bytes with
        | Nil -> Rejected (TruncatedOperand pc)
        | Cons (operand, tail) ->
          prepend_instruction
            (make_instruction pc (OpLoad (byte_nat operand)))
            (scan (ExpectOpcode (add pc (S (S O)))) tail))
     | StoreOperand ->
       (match bytes with
        | Nil -> Rejected (TruncatedOperand pc)
        | Cons (operand, tail) ->
          prepend_instruction
            (make_instruction pc (OpStore (byte_nat operand)))
            (scan (ExpectOpcode (add pc (S (S O)))) tail)))

type program = { program_bytes : Byte.t list; program_code : instruction list }

(** val parse : Byte.t list -> program parse_result **)

let parse bytes =
  match scan (ExpectOpcode O) bytes with
  | Parsed code0 -> Parsed { program_bytes = bytes; program_code = code0 }
  | Rejected error -> Rejected error

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type string =
| EmptyString
| String of ascii * string

(** val zeq : z -> z -> sumbool **)

let zeq =
  Z.eq_dec

(** val zlt : z -> z -> sumbool **)

let zlt =
  z_lt_dec

(** val zle : z -> z -> sumbool **)

let zle =
  z_le_gt_dec

(** val proj_sumbool : sumbool -> bool **)

let proj_sumbool = function
| Left -> True
| Right -> False

(** val p_mod_two_p : positive -> nat -> z **)

let rec p_mod_two_p p = function
| O -> Z0
| S m ->
  (match p with
   | XI q -> Z.succ_double (p_mod_two_p q m)
   | XO q -> Z.double (p_mod_two_p q m)
   | XH -> Zpos XH)

(** val zshiftin : bool -> z -> z **)

let zshiftin b x =
  match b with
  | True -> Z.succ_double x
  | False -> Z.double x

(** val zzero_ext : z -> z -> z **)

let zzero_ext n0 x =
  Z.iter n0 (fun rec0 x0 -> zshiftin (Z.odd x0) (rec0 (Z.div2 x0))) (fun _ ->
    Z0) x

(** val zsign_ext : z -> z -> z **)

let zsign_ext n0 x =
  Z.iter (Z.pred n0) (fun rec0 x0 -> zshiftin (Z.odd x0) (rec0 (Z.div2 x0)))
    (fun x0 ->
    match match Z.odd x0 with
          | True -> proj_sumbool (zlt Z0 n0)
          | False -> False with
    | True -> Zneg XH
    | False -> Z0) x

(** val z_one_bits : nat -> z -> z -> z list **)

let rec z_one_bits n0 x i =
  match n0 with
  | O -> Nil
  | S m ->
    (match Z.odd x with
     | True -> Cons (i, (z_one_bits m (Z.div2 x) (Z.add i (Zpos XH))))
     | False -> z_one_bits m (Z.div2 x) (Z.add i (Zpos XH)))

(** val p_is_power2 : positive -> bool **)

let rec p_is_power2 = function
| XI _ -> False
| XO q -> p_is_power2 q
| XH -> True

(** val z_is_power2 : z -> z option **)

let z_is_power2 x = match x with
| Zpos p -> (match p_is_power2 p with
             | True -> Some (Z.log2 x)
             | False -> None)
| _ -> None

(** val zsize : z -> z **)

let zsize = function
| Zpos p -> Zpos (Coq_Pos.size p)
| _ -> Z0

type binary_float =
| B754_zero of bool
| B754_infinity of bool
| B754_nan of bool * positive
| B754_finite of bool * positive * z

type binary32 = binary_float

type binary64 = binary_float

(** val ptr64 : bool **)

let ptr64 =
  True

type comparison0 =
| Ceq
| Cne
| Clt
| Cle
| Cgt
| Cge

module type WORDSIZE =
 sig
  val wordsize : nat
 end

module Make =
 functor (WS:WORDSIZE) ->
 struct
  (** val wordsize : nat **)

  let wordsize =
    WS.wordsize

  (** val zwordsize : z **)

  let zwordsize =
    Z.of_nat wordsize

  (** val modulus : z **)

  let modulus =
    two_power_nat wordsize

  (** val half_modulus : z **)

  let half_modulus =
    Z.div modulus (Zpos (XO XH))

  (** val max_unsigned : z **)

  let max_unsigned =
    Z.sub modulus (Zpos XH)

  (** val max_signed : z **)

  let max_signed =
    Z.sub half_modulus (Zpos XH)

  (** val min_signed : z **)

  let min_signed =
    Z.opp half_modulus

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  (** val intval : int -> z **)

  let intval i =
    i

  (** val coq_Z_mod_modulus : z -> z **)

  let coq_Z_mod_modulus = function
  | Z0 -> Z0
  | Zpos p -> p_mod_two_p p wordsize
  | Zneg p ->
    let r = p_mod_two_p p wordsize in
    (match zeq r Z0 with
     | Left -> Z0
     | Right -> Z.sub modulus r)

  (** val unsigned : int -> z **)

  let unsigned n0 =
    n0

  (** val signed : int -> z **)

  let signed n0 =
    let x = unsigned n0 in
    (match zlt x half_modulus with
     | Left -> x
     | Right -> Z.sub x modulus)

  (** val repr : z -> int **)

  let repr =
    coq_Z_mod_modulus

  (** val zero : int **)

  let zero =
    repr Z0

  (** val one : int **)

  let one =
    repr (Zpos XH)

  (** val mone : int **)

  let mone =
    repr (Zneg XH)

  (** val iwordsize : int **)

  let iwordsize =
    repr zwordsize

  (** val eq_dec : int -> int -> sumbool **)

  let eq_dec =
    zeq

  (** val eq : int -> int -> bool **)

  let eq x y =
    match zeq (unsigned x) (unsigned y) with
    | Left -> True
    | Right -> False

  (** val lt : int -> int -> bool **)

  let lt x y =
    match zlt (signed x) (signed y) with
    | Left -> True
    | Right -> False

  (** val ltu : int -> int -> bool **)

  let ltu x y =
    match zlt (unsigned x) (unsigned y) with
    | Left -> True
    | Right -> False

  (** val neg : int -> int **)

  let neg x =
    repr (Z.opp (unsigned x))

  (** val add : int -> int -> int **)

  let add x y =
    repr (Z.add (unsigned x) (unsigned y))

  (** val sub : int -> int -> int **)

  let sub x y =
    repr (Z.sub (unsigned x) (unsigned y))

  (** val mul : int -> int -> int **)

  let mul x y =
    repr (Z.mul (unsigned x) (unsigned y))

  (** val divs : int -> int -> int **)

  let divs x y =
    repr (Z.quot (signed x) (signed y))

  (** val mods : int -> int -> int **)

  let mods x y =
    repr (Z.rem (signed x) (signed y))

  (** val divu : int -> int -> int **)

  let divu x y =
    repr (Z.div (unsigned x) (unsigned y))

  (** val modu : int -> int -> int **)

  let modu x y =
    repr (Z.modulo (unsigned x) (unsigned y))

  (** val coq_and : int -> int -> int **)

  let coq_and x y =
    repr (Z.coq_land (unsigned x) (unsigned y))

  (** val coq_or : int -> int -> int **)

  let coq_or x y =
    repr (Z.coq_lor (unsigned x) (unsigned y))

  (** val xor : int -> int -> int **)

  let xor x y =
    repr (Z.coq_lxor (unsigned x) (unsigned y))

  (** val not : int -> int **)

  let not x =
    xor x mone

  (** val shl : int -> int -> int **)

  let shl x y =
    repr (Z.shiftl (unsigned x) (unsigned y))

  (** val shru : int -> int -> int **)

  let shru x y =
    repr (Z.shiftr (unsigned x) (unsigned y))

  (** val shr : int -> int -> int **)

  let shr x y =
    repr (Z.shiftr (signed x) (unsigned y))

  (** val rol : int -> int -> int **)

  let rol x y =
    let n0 = Z.modulo (unsigned y) zwordsize in
    repr
      (Z.coq_lor (Z.shiftl (unsigned x) n0)
        (Z.shiftr (unsigned x) (Z.sub zwordsize n0)))

  (** val ror : int -> int -> int **)

  let ror x y =
    let n0 = Z.modulo (unsigned y) zwordsize in
    repr
      (Z.coq_lor (Z.shiftr (unsigned x) n0)
        (Z.shiftl (unsigned x) (Z.sub zwordsize n0)))

  (** val rolm : int -> int -> int -> int **)

  let rolm x a m =
    coq_and (rol x a) m

  (** val shrx : int -> int -> int **)

  let shrx x y =
    divs x (shl one y)

  (** val mulhu : int -> int -> int **)

  let mulhu x y =
    repr (Z.div (Z.mul (unsigned x) (unsigned y)) modulus)

  (** val mulhs : int -> int -> int **)

  let mulhs x y =
    repr (Z.div (Z.mul (signed x) (signed y)) modulus)

  (** val negative : int -> int **)

  let negative x =
    match lt x zero with
    | True -> one
    | False -> zero

  (** val add_carry : int -> int -> int -> int **)

  let add_carry x y cin =
    match zlt (Z.add (Z.add (unsigned x) (unsigned y)) (unsigned cin)) modulus with
    | Left -> zero
    | Right -> one

  (** val add_overflow : int -> int -> int -> int **)

  let add_overflow x y cin =
    let s = Z.add (Z.add (signed x) (signed y)) (signed cin) in
    (match match proj_sumbool (zle min_signed s) with
           | True -> proj_sumbool (zle s max_signed)
           | False -> False with
     | True -> zero
     | False -> one)

  (** val sub_borrow : int -> int -> int -> int **)

  let sub_borrow x y bin =
    match zlt (Z.sub (Z.sub (unsigned x) (unsigned y)) (unsigned bin)) Z0 with
    | Left -> one
    | Right -> zero

  (** val sub_overflow : int -> int -> int -> int **)

  let sub_overflow x y bin =
    let s = Z.sub (Z.sub (signed x) (signed y)) (signed bin) in
    (match match proj_sumbool (zle min_signed s) with
           | True -> proj_sumbool (zle s max_signed)
           | False -> False with
     | True -> zero
     | False -> one)

  (** val shr_carry : int -> int -> int **)

  let shr_carry x y =
    match match lt x zero with
          | True -> negb (eq (coq_and x (sub (shl one y) one)) zero)
          | False -> False with
    | True -> one
    | False -> zero

  (** val zero_ext : z -> int -> int **)

  let zero_ext n0 x =
    repr (zzero_ext n0 (unsigned x))

  (** val sign_ext : z -> int -> int **)

  let sign_ext n0 x =
    repr (zsign_ext n0 (unsigned x))

  (** val one_bits : int -> int list **)

  let one_bits x =
    map repr (z_one_bits wordsize (unsigned x) Z0)

  (** val is_power2 : int -> int option **)

  let is_power2 x =
    match z_is_power2 (unsigned x) with
    | Some i -> Some (repr i)
    | None -> None

  (** val cmp : comparison0 -> int -> int -> bool **)

  let cmp c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> lt x y
    | Cle -> negb (lt y x)
    | Cgt -> lt y x
    | Cge -> negb (lt x y)

  (** val cmpu : comparison0 -> int -> int -> bool **)

  let cmpu c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> ltu x y
    | Cle -> negb (ltu y x)
    | Cgt -> ltu y x
    | Cge -> negb (ltu x y)

  (** val notbool : int -> int **)

  let notbool x =
    match eq x zero with
    | True -> one
    | False -> zero

  (** val divmodu2 : int -> int -> int -> (int, int) prod option **)

  let divmodu2 nhi nlo d =
    match eq_dec d zero with
    | Left -> None
    | Right ->
      let Pair (q, r) =
        Z.div_eucl (Z.add (Z.mul (unsigned nhi) modulus) (unsigned nlo))
          (unsigned d)
      in
      (match zle q max_unsigned with
       | Left -> Some (Pair ((repr q), (repr r)))
       | Right -> None)

  (** val divmods2 : int -> int -> int -> (int, int) prod option **)

  let divmods2 nhi nlo d =
    match eq_dec d zero with
    | Left -> None
    | Right ->
      let Pair (q, r) =
        Z.quotrem (Z.add (Z.mul (signed nhi) modulus) (unsigned nlo))
          (signed d)
      in
      (match match proj_sumbool (zle min_signed q) with
             | True -> proj_sumbool (zle q max_signed)
             | False -> False with
       | True -> Some (Pair ((repr q), (repr r)))
       | False -> None)

  (** val testbit : int -> z -> bool **)

  let testbit x i =
    Z.testbit (unsigned x) i

  (** val int_of_one_bits : int list -> int **)

  let rec int_of_one_bits = function
  | Nil -> zero
  | Cons (a, b) -> add (shl one a) (int_of_one_bits b)

  (** val no_overlap : int -> z -> int -> z -> bool **)

  let no_overlap ofs1 sz1 ofs2 sz2 =
    let x1 = unsigned ofs1 in
    let x2 = unsigned ofs2 in
    (match match proj_sumbool (zlt (Z.add x1 sz1) modulus) with
           | True -> proj_sumbool (zlt (Z.add x2 sz2) modulus)
           | False -> False with
     | True ->
       (match proj_sumbool (zle (Z.add x1 sz1) x2) with
        | True -> True
        | False -> proj_sumbool (zle (Z.add x2 sz2) x1))
     | False -> False)

  (** val size : int -> z **)

  let size x =
    zsize (unsigned x)

  (** val unsigned_bitfield_extract : z -> z -> int -> int **)

  let unsigned_bitfield_extract pos width n0 =
    zero_ext width (shru n0 (repr pos))

  (** val signed_bitfield_extract : z -> z -> int -> int **)

  let signed_bitfield_extract pos width n0 =
    sign_ext width (shru n0 (repr pos))

  (** val bitfield_insert : z -> z -> int -> int -> int **)

  let bitfield_insert pos width n0 p =
    let mask0 = shl (repr (Z.sub (two_p width) (Zpos XH))) (repr pos) in
    coq_or (shl (zero_ext width p) (repr pos)) (coq_and n0 (not mask0))
 end

module Wordsize_32 =
 struct
  (** val wordsize : nat **)

  let wordsize =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
 end

module Int = Make(Wordsize_32)

module Wordsize_64 =
 struct
  (** val wordsize : nat **)

  let wordsize =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 end

module Int64 =
 struct
  (** val wordsize : nat **)

  let wordsize =
    Wordsize_64.wordsize

  (** val modulus : z **)

  let modulus =
    two_power_nat wordsize

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  (** val coq_Z_mod_modulus : z -> z **)

  let coq_Z_mod_modulus = function
  | Z0 -> Z0
  | Zpos p -> p_mod_two_p p wordsize
  | Zneg p ->
    let r = p_mod_two_p p wordsize in
    (match zeq r Z0 with
     | Left -> Z0
     | Right -> Z.sub modulus r)

  (** val repr : z -> int **)

  let repr =
    coq_Z_mod_modulus
 end

module Wordsize_Ptrofs =
 struct
  (** val wordsize : nat **)

  let wordsize =
    match ptr64 with
    | True ->
      S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | False ->
      S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
 end

module Ptrofs =
 struct
  (** val wordsize : nat **)

  let wordsize =
    Wordsize_Ptrofs.wordsize

  (** val modulus : z **)

  let modulus =
    two_power_nat wordsize

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  (** val coq_Z_mod_modulus : z -> z **)

  let coq_Z_mod_modulus = function
  | Z0 -> Z0
  | Zpos p -> p_mod_two_p p wordsize
  | Zneg p ->
    let r = p_mod_two_p p wordsize in
    (match zeq r Z0 with
     | Left -> Z0
     | Right -> Z.sub modulus r)

  (** val repr : z -> int **)

  let repr =
    coq_Z_mod_modulus
 end

type float = binary64

type float32 = binary32

type ident = positive

type typ =
| Tint
| Tfloat
| Tlong
| Tsingle
| Tany32
| Tany64

type xtype =
| Xbool
| Xint8signed
| Xint8unsigned
| Xint16signed
| Xint16unsigned
| Xint
| Xfloat
| Xlong
| Xsingle
| Xptr
| Xany32
| Xany64
| Xvoid

type calling_convention = { cc_vararg : z option; cc_unproto : bool;
                            cc_structret : bool }

(** val cc_default : calling_convention **)

let cc_default =
  { cc_vararg = None; cc_unproto = False; cc_structret = False }

type signature = { sig_args : xtype list; sig_res : xtype;
                   sig_cc : calling_convention }

type memory_chunk =
| Mbool
| Mint8signed
| Mint8unsigned
| Mint16signed
| Mint16unsigned
| Mint32
| Mint64
| Mfloat32
| Mfloat64
| Many32
| Many64

type external_function =
| EF_external of string * signature
| EF_builtin of string * signature
| EF_runtime of string * signature
| EF_vload of memory_chunk
| EF_vstore of memory_chunk
| EF_malloc
| EF_free
| EF_memcpy of z * z
| EF_annot of positive * string * typ list
| EF_annot_val of positive * string * typ
| EF_inline_asm of string * signature * string list
| EF_debug of positive * ident * typ list

type 'a builtin_arg =
| BA of 'a
| BA_int of Int.int
| BA_long of Int64.int
| BA_float of float
| BA_single of float32
| BA_loadstack of memory_chunk * Ptrofs.int
| BA_addrstack of Ptrofs.int
| BA_loadglobal of memory_chunk * ident * Ptrofs.int
| BA_addrglobal of ident * Ptrofs.int
| BA_splitlong of 'a builtin_arg * 'a builtin_arg
| BA_addptr of 'a builtin_arg * 'a builtin_arg

type 'a builtin_res =
| BR of 'a
| BR_none
| BR_splitlong of 'a builtin_res * 'a builtin_res

type ireg =
| RAX
| RBX
| RCX
| RDX
| RSI
| RDI
| RBP
| RSP
| R8
| R9
| R10
| R11
| R12
| R13
| R14
| R15

type freg =
| XMM0
| XMM1
| XMM2
| XMM3
| XMM4
| XMM5
| XMM6
| XMM7
| XMM8
| XMM9
| XMM10
| XMM11
| XMM12
| XMM13
| XMM14
| XMM15

type crbit =
| ZF
| CF
| PF
| SF
| OF

type preg =
| PC
| IR of ireg
| FR of freg
| ST0
| CR of crbit
| RA

type label = positive

type addrmode =
| Addrmode of ireg option * (ireg, z) prod option
   * (z, (ident, Ptrofs.int) prod) sum

type testcond =
| Cond_e
| Cond_ne
| Cond_b
| Cond_be
| Cond_ae
| Cond_a
| Cond_l
| Cond_le
| Cond_ge
| Cond_g
| Cond_p
| Cond_np

type instruction0 =
| Pmov_rr of ireg * ireg
| Pmovl_ri of ireg * Int.int
| Pmovq_ri of ireg * Int64.int
| Pmov_rs of ireg * ident
| Pmovl_rm of ireg * addrmode
| Pmovq_rm of ireg * addrmode
| Pmovl_mr of addrmode * ireg
| Pmovq_mr of addrmode * ireg
| Pmovsd_ff of freg * freg
| Pmovsd_fi of freg * float
| Pmovsd_fm of freg * addrmode
| Pmovsd_mf of addrmode * freg
| Pmovss_fi of freg * float32
| Pmovss_fm of freg * addrmode
| Pmovss_mf of addrmode * freg
| Pfldl_m of addrmode
| Pfstpl_m of addrmode
| Pflds_m of addrmode
| Pfstps_m of addrmode
| Pmovb_mr of addrmode * ireg
| Pmovw_mr of addrmode * ireg
| Pmovzb_rr of ireg * ireg
| Pmovzb_rm of ireg * addrmode
| Pmovsb_rr of ireg * ireg
| Pmovsb_rm of ireg * addrmode
| Pmovzw_rr of ireg * ireg
| Pmovzw_rm of ireg * addrmode
| Pmovsw_rr of ireg * ireg
| Pmovsw_rm of ireg * addrmode
| Pmovzl_rr of ireg * ireg
| Pmovsl_rr of ireg * ireg
| Pmovls_rr of ireg
| Pcvtsd2ss_ff of freg * freg
| Pcvtss2sd_ff of freg * freg
| Pcvttsd2si_rf of ireg * freg
| Pcvtsi2sd_fr of freg * ireg
| Pcvttss2si_rf of ireg * freg
| Pcvtsi2ss_fr of freg * ireg
| Pcvttsd2sl_rf of ireg * freg
| Pcvtsl2sd_fr of freg * ireg
| Pcvttss2sl_rf of ireg * freg
| Pcvtsl2ss_fr of freg * ireg
| Pleal of ireg * addrmode
| Pleaq of ireg * addrmode
| Pnegl of ireg
| Pnegq of ireg
| Paddl_ri of ireg * Int.int
| Paddq_ri of ireg * Int64.int
| Psubl_rr of ireg * ireg
| Psubq_rr of ireg * ireg
| Pimull_rr of ireg * ireg
| Pimulq_rr of ireg * ireg
| Pimull_ri of ireg * Int.int
| Pimulq_ri of ireg * Int64.int
| Pimull_r of ireg
| Pimulq_r of ireg
| Pmull_r of ireg
| Pmulq_r of ireg
| Pcltd
| Pcqto
| Pdivl of ireg
| Pdivq of ireg
| Pidivl of ireg
| Pidivq of ireg
| Pandl_rr of ireg * ireg
| Pandq_rr of ireg * ireg
| Pandl_ri of ireg * Int.int
| Pandq_ri of ireg * Int64.int
| Porl_rr of ireg * ireg
| Porq_rr of ireg * ireg
| Porl_ri of ireg * Int.int
| Porq_ri of ireg * Int64.int
| Pxorl_r of ireg
| Pxorq_r of ireg
| Pxorl_rr of ireg * ireg
| Pxorq_rr of ireg * ireg
| Pxorl_ri of ireg * Int.int
| Pxorq_ri of ireg * Int64.int
| Pnotl of ireg
| Pnotq of ireg
| Psall_rcl of ireg
| Psalq_rcl of ireg
| Psall_ri of ireg * Int.int
| Psalq_ri of ireg * Int.int
| Pshrl_rcl of ireg
| Pshrq_rcl of ireg
| Pshrl_ri of ireg * Int.int
| Pshrq_ri of ireg * Int.int
| Psarl_rcl of ireg
| Psarq_rcl of ireg
| Psarl_ri of ireg * Int.int
| Psarq_ri of ireg * Int.int
| Pshld_ri of ireg * ireg * Int.int
| Prorl_ri of ireg * Int.int
| Prorq_ri of ireg * Int.int
| Pcmpl_rr of ireg * ireg
| Pcmpq_rr of ireg * ireg
| Pcmpl_ri of ireg * Int.int
| Pcmpq_ri of ireg * Int64.int
| Ptestl_rr of ireg * ireg
| Ptestq_rr of ireg * ireg
| Ptestl_ri of ireg * Int.int
| Ptestq_ri of ireg * Int64.int
| Pcmov of testcond * ireg * ireg
| Psetcc of testcond * ireg
| Paddd_ff of freg * freg
| Psubd_ff of freg * freg
| Pmuld_ff of freg * freg
| Pdivd_ff of freg * freg
| Pnegd of freg
| Pabsd of freg
| Pcomisd_ff of freg * freg
| Pxorpd_f of freg
| Padds_ff of freg * freg
| Psubs_ff of freg * freg
| Pmuls_ff of freg * freg
| Pdivs_ff of freg * freg
| Pnegs of freg
| Pabss of freg
| Pcomiss_ff of freg * freg
| Pxorps_f of freg
| Pjmp_l of label
| Pjmp_s of ident * signature
| Pjmp_r of ireg * signature
| Pjcc of testcond * label
| Pjcc2 of testcond * testcond * label
| Pjmptbl of ireg * label list
| Pcall_s of ident * signature
| Pcall_r of ireg * signature
| Pret
| Pmov_rm_a of ireg * addrmode
| Pmov_mr_a of addrmode * ireg
| Pmovsd_fm_a of freg * addrmode
| Pmovsd_mf_a of addrmode * freg
| Plabel of label
| Pallocframe of z * Ptrofs.int * Ptrofs.int
| Pfreeframe of z * Ptrofs.int * Ptrofs.int
| Pbuiltin of external_function * preg builtin_arg list * preg builtin_res
| Padcl_ri of ireg * Int.int
| Padcl_rr of ireg * ireg
| Paddl_mi of addrmode * Int.int
| Paddl_rr of ireg * ireg
| Pbsfl of ireg * ireg
| Pbsfq of ireg * ireg
| Pbsrl of ireg * ireg
| Pbsrq of ireg * ireg
| Pbswap64 of ireg
| Pbswap32 of ireg
| Pbswap16 of ireg
| Pcfi_adjust of Int.int
| Pfmadd132 of freg * freg * freg
| Pfmadd213 of freg * freg * freg
| Pfmadd231 of freg * freg * freg
| Pfmsub132 of freg * freg * freg
| Pfmsub213 of freg * freg * freg
| Pfmsub231 of freg * freg * freg
| Pfnmadd132 of freg * freg * freg
| Pfnmadd213 of freg * freg * freg
| Pfnmadd231 of freg * freg * freg
| Pfnmsub132 of freg * freg * freg
| Pfnmsub213 of freg * freg * freg
| Pfnmsub231 of freg * freg * freg
| Pmaxsd of freg * freg
| Pminsd of freg * freg
| Pmovb_rm of ireg * addrmode
| Pmovq_rf of ireg * freg
| Pmovsq_mr of addrmode * freg
| Pmovsq_rm of freg * addrmode
| Pmovsb
| Pmovsw
| Pmovw_rm of ireg * addrmode
| Pnop
| Prep_movsl
| Psbbl_rr of ireg * ireg
| Psqrtsd of freg * freg
| Psubl_ri of ireg * Int.int
| Psubq_ri of ireg * Int64.int

type code = instruction0 list

type function0 = { fn_sig : signature; fn_code : code }

(** val bytecode_signature : signature **)

let bytecode_signature =
  { sig_args = (Cons (Xptr, (Cons (Xint, (Cons (Xptr, (Cons (Xint,
    Nil)))))))); sig_res = Xvoid; sig_cc = cc_default }

(** val word_bytes : z **)

let word_bytes =
  Zpos (XO (XO (XO (XO (XO XH)))))

(** val word_limb_bytes : z **)

let word_limb_bytes =
  Zpos (XO (XO XH))

(** val word_limb_count : nat **)

let word_limb_count =
  S (S (S (S (S (S (S (S O)))))))

(** val native_stack_limit_words : z **)

let native_stack_limit_words =
  Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO XH))))))))))

(** val frame_link_offset : z **)

let frame_link_offset =
  Z0

(** val frame_ra_offset : z **)

let frame_ra_offset =
  Zpos (XO (XO (XO XH)))

(** val frame_stack_base : z **)

let frame_stack_base =
  Zpos (XO (XO (XO (XO XH))))

(** val frame_stack_bytes : z **)

let frame_stack_bytes =
  Z.mul native_stack_limit_words word_bytes

(** val frame_size : z **)

let frame_size =
  Z.add frame_stack_base frame_stack_bytes

(** val frame_link_ptrofs : Ptrofs.int **)

let frame_link_ptrofs =
  Ptrofs.repr frame_link_offset

(** val frame_ra_ptrofs : Ptrofs.int **)

let frame_ra_ptrofs =
  Ptrofs.repr frame_ra_offset

(** val arg_in : ireg **)

let arg_in =
  RDI

(** val arg_insize : ireg **)

let arg_insize =
  RSI

(** val arg_out : ireg **)

let arg_out =
  RDX

(** val arg_outsize : ireg **)

let arg_outsize =
  RCX

(** val stack_ptr_reg : ireg **)

let stack_ptr_reg =
  R8

(** val tmp0 : ireg **)

let tmp0 =
  R9

(** val tmp1 : ireg **)

let tmp1 =
  R10

(** val as_int : z -> Int.int **)

let as_int =
  Int.repr

(** val as_int64 : z -> Int64.int **)

let as_int64 =
  Int64.repr

(** val reg_addr : ireg -> z -> addrmode **)

let reg_addr base ofs =
  Addrmode ((Some base), None, (Inl ofs))

(** val pc_label : nat -> label **)

let pc_label =
  Coq_Pos.of_succ_nat

(** val label_span : program -> nat **)

let label_span p =
  S (length p.program_bytes)

(** val local_label : program -> nat -> nat -> nat -> label **)

let local_label p tag pc slot =
  Coq_Pos.of_succ_nat
    (add
      (add
        (add (length p.program_bytes)
          (mul (mul tag (label_span p)) (label_span p)))
        (mul pc (label_span p)))
      slot)

(** val halt_label : program -> label **)

let halt_label p =
  local_label p (S O) O O

(** val jump_zero_label : program -> nat -> label **)

let jump_zero_label p pc =
  local_label p (S (S O)) pc O

(** val jump_case_label : program -> nat -> nat -> label **)

let jump_case_label p pc case_index =
  local_label p (S (S (S O))) pc case_index

(** val limb_offset : nat -> z **)

let limb_offset limb =
  Z.mul word_limb_bytes (Z.of_nat limb)

(** val internal_word_offset : nat -> nat -> z **)

let internal_word_offset word_index limb =
  Z.add (Z.mul word_bytes (Z.of_nat word_index)) (limb_offset limb)

(** val external_word_offset : nat -> nat -> z **)

let external_word_offset word_index limb =
  Z.add (Z.mul word_bytes (Z.of_nat word_index))
    (Z.mul word_limb_bytes
      (Z.of_nat (sub (S (S (S (S (S (S (S O))))))) limb)))

(** val frame_stack_end : z **)

let frame_stack_end =
  Z.add frame_stack_base frame_stack_bytes

(** val word_limb : z -> nat -> z **)

let word_limb value limb =
  Z.coq_land
    (Z.shiftr value
      (Z.mul (Zpos (XO (XO (XO (XO (XO XH)))))) (Z.of_nat limb)))
    (Z.ones (Zpos (XO (XO (XO (XO (XO XH)))))))

(** val word_limb_int : z -> nat -> Int.int **)

let word_limb_int value limb =
  as_int (word_limb value limb)

(** val all_limbs : nat list **)

let all_limbs =
  seq O word_limb_count

(** val compile_limb_code : (nat -> code) -> nat list -> code **)

let rec compile_limb_code f = function
| Nil -> Nil
| Cons (limb, rest) -> app (f limb) (compile_limb_code f rest)

(** val jumpdest_pcs : program -> nat list **)

let jumpdest_pcs p =
  fold_right (fun i acc ->
    match i.instr_opcode with
    | OpJumpdest -> Cons (i.instr_pc, acc)
    | _ -> acc) Nil p.program_code

(** val init_stack_pointer : code **)

let init_stack_pointer =
  Cons ((Pleaq (stack_ptr_reg, (reg_addr RSP frame_stack_base))), Nil)

(** val halt_if_stack_full : label -> code **)

let halt_if_stack_full halt =
  Cons ((Pleaq (tmp0, (reg_addr RSP frame_stack_end))), (Cons ((Pcmpq_rr
    (stack_ptr_reg, tmp0)), (Cons ((Pjcc (Cond_ae, halt)), Nil)))))

(** val halt_if_stack_below : z -> label -> code **)

let halt_if_stack_below required_bytes halt =
  Cons ((Pleaq (tmp0,
    (reg_addr RSP (Z.add frame_stack_base required_bytes)))), (Cons
    ((Pcmpq_rr (stack_ptr_reg, tmp0)), (Cons ((Pjcc (Cond_b, halt)), Nil)))))

(** val halt_if_input_oob : nat -> label -> code **)

let halt_if_input_oob index halt =
  Cons ((Pcmpq_ri (arg_insize, (as_int64 (Z.of_nat index)))), (Cons ((Pjcc
    (Cond_be, halt)), Nil)))

(** val halt_if_output_oob : nat -> label -> code **)

let halt_if_output_oob index halt =
  Cons ((Pcmpq_ri (arg_outsize, (as_int64 (Z.of_nat index)))), (Cons ((Pjcc
    (Cond_be, halt)), Nil)))

(** val load_external_word : ireg -> nat -> ireg -> nat -> code **)

let load_external_word src_base src_index dst_base dst_word_index =
  compile_limb_code (fun limb -> Cons ((Pmovl_rm (tmp0,
    (reg_addr src_base (external_word_offset src_index limb)))), (Cons
    ((Pbswap32 tmp0), (Cons ((Pmovl_mr
    ((reg_addr dst_base (internal_word_offset dst_word_index limb)), tmp0)),
    Nil)))))) all_limbs

(** val store_external_word_from_offset : ireg -> z -> ireg -> nat -> code **)

let store_external_word_from_offset src_base src_ofs dst_base dst_index =
  compile_limb_code (fun limb -> Cons ((Pmovl_rm (tmp0,
    (reg_addr src_base (Z.add src_ofs (limb_offset limb))))), (Cons
    ((Pbswap32 tmp0), (Cons ((Pmovl_mr
    ((reg_addr dst_base (external_word_offset dst_index limb)), tmp0)),
    Nil)))))) all_limbs

(** val copy_internal_word_from_offset : ireg -> z -> ireg -> nat -> code **)

let copy_internal_word_from_offset src_base src_ofs dst_base dst_word_index =
  compile_limb_code (fun limb -> Cons ((Pmovl_rm (tmp0,
    (reg_addr src_base (Z.add src_ofs (limb_offset limb))))), (Cons
    ((Pmovl_mr
    ((reg_addr dst_base (internal_word_offset dst_word_index limb)), tmp0)),
    Nil)))) all_limbs

(** val add_top_words : code **)

let add_top_words =
  app (Cons ((Pmovl_rm (tmp0,
    (reg_addr stack_ptr_reg (Zneg (XO (XO (XO (XO (XO (XO XH)))))))))), (Cons
    ((Pmovl_rm (tmp1,
    (reg_addr stack_ptr_reg (Zneg (XO (XO (XO (XO (XO XH))))))))), (Cons
    ((Paddl_rr (tmp0, tmp1)), (Cons ((Pmovl_mr
    ((reg_addr stack_ptr_reg (Zneg (XO (XO (XO (XO (XO (XO XH)))))))),
    tmp0)), Nil))))))))
    (app
      (compile_limb_code (fun limb -> Cons ((Pmovl_rm (tmp0,
        (reg_addr stack_ptr_reg
          (Z.add (Zneg (XO (XO (XO (XO (XO (XO XH)))))))
            (limb_offset (S limb)))))),
        (Cons ((Pmovl_rm (tmp1,
        (reg_addr stack_ptr_reg
          (Z.add (Zneg (XO (XO (XO (XO (XO XH)))))) (limb_offset (S limb)))))),
        (Cons ((Padcl_rr (tmp0, tmp1)), (Cons ((Pmovl_mr
        ((reg_addr stack_ptr_reg
           (Z.add (Zneg (XO (XO (XO (XO (XO (XO XH)))))))
             (limb_offset (S limb)))),
        tmp0)), Nil)))))))) (seq O (S (S (S (S (S (S (S O)))))))))
      (Cons ((Psubq_ri (stack_ptr_reg, (as_int64 word_bytes))), Nil)))

(** val sub_top_words : code **)

let sub_top_words =
  app (Cons ((Pmovl_rm (tmp0,
    (reg_addr stack_ptr_reg (Zneg (XO (XO (XO (XO (XO (XO XH)))))))))), (Cons
    ((Pmovl_rm (tmp1,
    (reg_addr stack_ptr_reg (Zneg (XO (XO (XO (XO (XO XH))))))))), (Cons
    ((Psubl_rr (tmp0, tmp1)), (Cons ((Pmovl_mr
    ((reg_addr stack_ptr_reg (Zneg (XO (XO (XO (XO (XO (XO XH)))))))),
    tmp0)), Nil))))))))
    (app
      (compile_limb_code (fun limb -> Cons ((Pmovl_rm (tmp0,
        (reg_addr stack_ptr_reg
          (Z.add (Zneg (XO (XO (XO (XO (XO (XO XH)))))))
            (limb_offset (S limb)))))),
        (Cons ((Pmovl_rm (tmp1,
        (reg_addr stack_ptr_reg
          (Z.add (Zneg (XO (XO (XO (XO (XO XH)))))) (limb_offset (S limb)))))),
        (Cons ((Psbbl_rr (tmp0, tmp1)), (Cons ((Pmovl_mr
        ((reg_addr stack_ptr_reg
           (Z.add (Zneg (XO (XO (XO (XO (XO (XO XH)))))))
             (limb_offset (S limb)))),
        tmp0)), Nil)))))))) (seq O (S (S (S (S (S (S (S O)))))))))
      (Cons ((Psubq_ri (stack_ptr_reg, (as_int64 word_bytes))), Nil)))

(** val zero_test_word_at : ireg -> z -> label -> code **)

let zero_test_word_at base ofs on_zero =
  app (Cons ((Pxorl_r tmp0), Nil))
    (app
      (compile_limb_code (fun limb -> Cons ((Pmovl_rm (tmp1,
        (reg_addr base (Z.add ofs (limb_offset limb))))), (Cons ((Porl_rr
        (tmp0, tmp1)), Nil)))) all_limbs)
      (Cons ((Ptestl_rr (tmp0, tmp0)), (Cons ((Pjcc (Cond_e, on_zero)),
      Nil)))))

(** val compare_word_at_with : ireg -> z -> z -> label -> code **)

let compare_word_at_with base ofs value on_mismatch =
  compile_limb_code (fun limb -> Cons ((Pmovl_rm (tmp0,
    (reg_addr base (Z.add ofs (limb_offset limb))))), (Cons ((Pcmpl_ri (tmp0,
    (word_limb_int value limb))), (Cons ((Pjcc (Cond_ne, on_mismatch)),
    Nil)))))) all_limbs

(** val compile_jump_cases : program -> nat -> nat -> nat list -> code **)

let rec compile_jump_cases p pc case_index = function
| Nil -> Cons ((Pjmp_l (halt_label p)), Nil)
| Cons (destination, rest) ->
  let miss = jump_case_label p pc case_index in
  app
    (compare_word_at_with stack_ptr_reg word_bytes (Z.of_nat destination)
      miss)
    (app (Cons ((Pjmp_l (pc_label destination)), (Cons ((Plabel miss),
      Nil)))) (compile_jump_cases p pc (S case_index) rest))

(** val compile_push_from_input : program -> nat -> code **)

let compile_push_from_input p index =
  app (halt_if_input_oob index (halt_label p))
    (app (halt_if_stack_full (halt_label p))
      (app (load_external_word arg_in index stack_ptr_reg O) (Cons ((Paddq_ri
        (stack_ptr_reg, (as_int64 word_bytes))), Nil))))

(** val compile_store_to_output : program -> nat -> code **)

let compile_store_to_output p index =
  app (halt_if_output_oob index (halt_label p))
    (app (halt_if_stack_below word_bytes (halt_label p))
      (app
        (store_external_word_from_offset stack_ptr_reg (Z.opp word_bytes)
          arg_out index)
        (Cons ((Psubq_ri (stack_ptr_reg, (as_int64 word_bytes))), Nil))))

(** val compile_dup : program -> code **)

let compile_dup p =
  app (halt_if_stack_below word_bytes (halt_label p))
    (app (halt_if_stack_full (halt_label p))
      (app
        (copy_internal_word_from_offset stack_ptr_reg (Z.opp word_bytes)
          stack_ptr_reg O)
        (Cons ((Paddq_ri (stack_ptr_reg, (as_int64 word_bytes))), Nil))))

(** val compile_jumpi : program -> nat -> code **)

let compile_jumpi p pc =
  app (halt_if_stack_below (Z.mul (Zpos (XO XH)) word_bytes) (halt_label p))
    (app
      (zero_test_word_at stack_ptr_reg (Zneg (XO (XO (XO (XO (XO (XO
        XH))))))) (jump_zero_label p pc))
      (app (Cons ((Psubq_ri (stack_ptr_reg,
        (as_int64 (Z.mul (Zpos (XO XH)) word_bytes)))), Nil))
        (app (compile_jump_cases p pc O (jumpdest_pcs p)) (Cons ((Plabel
          (jump_zero_label p pc)), (Cons ((Psubq_ri (stack_ptr_reg,
          (as_int64 (Z.mul (Zpos (XO XH)) word_bytes)))), Nil)))))))

(** val transl_instruction : program -> instruction -> code **)

let transl_instruction p i =
  match i.instr_opcode with
  | OpStop -> Cons ((Pjmp_l (halt_label p)), Nil)
  | OpLoad index -> compile_push_from_input p index
  | OpStore index -> compile_store_to_output p index
  | OpPop ->
    app (halt_if_stack_below word_bytes (halt_label p)) (Cons ((Psubq_ri
      (stack_ptr_reg, (as_int64 word_bytes))), Nil))
  | OpAdd ->
    app
      (halt_if_stack_below (Z.mul (Zpos (XO XH)) word_bytes) (halt_label p))
      add_top_words
  | OpSub ->
    app
      (halt_if_stack_below (Z.mul (Zpos (XO XH)) word_bytes) (halt_label p))
      sub_top_words
  | OpDup -> compile_dup p
  | OpJumpdest -> Nil
  | OpJumpi -> compile_jumpi p i.instr_pc

(** val transl_labeled_instruction : program -> instruction -> code **)

let transl_labeled_instruction p i =
  Cons ((Plabel (pc_label i.instr_pc)), (transl_instruction p i))

(** val transl_code : program -> instruction list -> code **)

let rec transl_code p = function
| Nil -> Nil
| Cons (i, rest) -> app (transl_labeled_instruction p i) (transl_code p rest)

(** val transl_program_code : program -> code **)

let transl_program_code p =
  app (Cons ((Pallocframe (frame_size, frame_ra_ptrofs, frame_link_ptrofs)),
    Nil))
    (app init_stack_pointer
      (app (transl_code p p.program_code) (Cons ((Plabel (halt_label p)),
        (Cons ((Pfreeframe (frame_size, frame_ra_ptrofs, frame_link_ptrofs)),
        (Cons (Pret, Nil))))))))

(** val transl_program : program -> function0 **)

let transl_program p =
  { fn_sig = bytecode_signature; fn_code = (transl_program_code p) }

(** val transl_bytes : Byte.t list -> function0 parse_result **)

let transl_bytes bytes =
  match parse bytes with
  | Parsed p -> Parsed (transl_program p)
  | Rejected error -> Rejected error
