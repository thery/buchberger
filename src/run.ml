
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type bool =
| True
| False

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

type 'a sumor =
| Inleft of 'a
| Inright

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

module Nat =
 struct
  (** val max : nat -> nat -> nat **)

  let rec max n m =
    match n with
    | O -> m
    | S n' -> (match m with
               | O -> n
               | S m' -> S (max n' m'))

  (** val eq_dec : nat -> nat -> sumbool **)

  let rec eq_dec n m =
    match n with
    | O -> (match m with
            | O -> Left
            | S _ -> Right)
    | S n0 -> (match m with
               | O -> Right
               | S n1 -> eq_dec n0 n1)
 end

(** val lt_eq_lt_dec : nat -> nat -> sumbool sumor **)

let rec lt_eq_lt_dec n m =
  match n with
  | O -> (match m with
          | O -> Inleft Right
          | S _ -> Inleft Left)
  | S n0 -> (match m with
             | O -> Inright
             | S n1 -> lt_eq_lt_dec n0 n1)

(** val le_lt_dec : nat -> nat -> sumbool **)

let rec le_lt_dec n m =
  match n with
  | O -> Left
  | S n0 -> (match m with
             | O -> Right
             | S n1 -> le_lt_dec n0 n1)

(** val le_lt_eq_dec : nat -> nat -> sumbool **)

let le_lt_eq_dec n m =
  let s = lt_eq_lt_dec n m in
  (match s with
   | Inleft s0 -> s0
   | Inright -> assert false (* absurd case *))

type mon =
| N_0
| C_n of nat * nat * mon

(** val pmon1 : nat -> mon -> nat **)

let pmon1 _ = function
| N_0 -> O
| C_n (_, n, _) -> n

(** val pmon2 : nat -> mon -> mon **)

let pmon2 _ = function
| N_0 -> N_0
| C_n (_, _, m0) -> m0

(** val gen_mon : nat -> nat -> mon **)

let rec gen_mon n n0 =
  match n with
  | O -> N_0
  | S n1 ->
    (match n0 with
     | O -> C_n (n1, (S O), (gen_mon n1 n1))
     | S n2 -> C_n (n1, O, (gen_mon n1 n2)))

(** val mult_mon : nat -> mon -> mon -> mon **)

let rec mult_mon n h' h'0 =
  match n with
  | O -> N_0
  | S n0 ->
    C_n (n0, (add (pmon1 (S n0) h') (pmon1 (S n0) h'0)),
      (mult_mon n0 (pmon2 (S n0) h') (pmon2 (S n0) h'0)))

(** val zero_mon : nat -> mon **)

let rec zero_mon = function
| O -> N_0
| S n0 -> C_n (n0, O, (zero_mon n0))

(** val div_mon : nat -> mon -> mon -> mon **)

let rec div_mon n h' h'0 =
  match n with
  | O -> N_0
  | S n0 ->
    C_n (n0, (sub (pmon1 (S n0) h') (pmon1 (S n0) h'0)),
      (div_mon n0 (pmon2 (S n0) h') (pmon2 (S n0) h'0)))

(** val div_mon_clean : nat -> mon -> mon -> (mon, bool) prod **)

let rec div_mon_clean n h' h'0 =
  match n with
  | O -> Pair (N_0, True)
  | S n0 ->
    (match le_lt_dec (pmon1 (S n0) h'0) (pmon1 (S n0) h') with
     | Left ->
       let Pair (m, b) = div_mon_clean n0 (pmon2 (S n0) h') (pmon2 (S n0) h'0)
       in
       Pair ((C_n (n0, (sub (pmon1 (S n0) h') (pmon1 (S n0) h'0)), m)), b)
     | Right -> Pair (h', False))

(** val eqmon_dec : nat -> mon -> mon -> sumbool **)

let rec eqmon_dec n x y =
  match n with
  | O -> Left
  | S n0 ->
    (match Nat.eq_dec (pmon1 (S n0) x) (pmon1 (S n0) y) with
     | Left -> eqmon_dec n0 (pmon2 (S n0) x) (pmon2 (S n0) y)
     | Right -> Right)

(** val ppcm_mon : nat -> mon -> mon -> mon **)

let rec ppcm_mon n m2 m3 =
  match n with
  | O -> N_0
  | S n0 ->
    C_n (n0, (Nat.max (pmon1 (S n0) m2) (pmon1 (S n0) m3)),
      (ppcm_mon n0 (pmon2 (S n0) m2) (pmon2 (S n0) m3)))

(** val letP : 'a1 -> ('a1 -> __ -> 'a2) -> 'a2 **)

let letP h h' =
  h' h __

(** val orderc_dec : nat -> mon -> mon -> sumbool sumor **)

let rec orderc_dec _ m b =
  match m with
  | N_0 -> Inright
  | C_n (d, n, m0) ->
    (match orderc_dec d m0 (pmon2 (S d) b) with
     | Inleft s -> Inleft s
     | Inright ->
       (match lt_eq_lt_dec n (pmon1 (S d) b) with
        | Inleft a -> (match a with
                       | Left -> Inleft Right
                       | Right -> Inright)
        | Inright -> Inleft Left))

(** val degc : nat -> mon -> nat **)

let rec degc _ = function
| N_0 -> O
| C_n (d, n, m0) -> add n (degc d m0)

(** val total_orderc_dec : nat -> mon -> mon -> sumbool sumor **)

let total_orderc_dec n a b =
  letP (degc n a) (fun u _ ->
    letP (degc n b) (fun u0 _ ->
      match le_lt_dec u u0 with
      | Left ->
        (match le_lt_eq_dec u u0 with
         | Left -> Inleft Left
         | Right -> orderc_dec n a b)
      | Right -> Inleft Right))

(** val m1 : nat -> mon **)

let m1 =
  zero_mon

type 'a term = ('a, mon) prod

(** val t2M : nat -> 'a1 term -> mon **)

let t2M _ = function
| Pair (_, m) -> m

(** val zeroP_dec :
    'a1 -> ('a1 -> 'a1 -> sumbool) -> nat -> 'a1 term -> sumbool **)

let zeroP_dec a0 eqA_dec _ = function
| Pair (a, _) -> eqA_dec a a0

(** val plusTerm :
    ('a1 -> 'a1 -> 'a1) -> nat -> 'a1 term -> 'a1 term -> 'a1 term **)

let plusTerm plusA _ x y =
  let Pair (a, m) = x in let Pair (a0, _) = y in Pair ((plusA a a0), m)

(** val multTerm :
    ('a1 -> 'a1 -> 'a1) -> nat -> 'a1 term -> 'a1 term -> 'a1 term **)

let multTerm multA n h' h1' =
  let Pair (a, m) = h' in
  let Pair (a0, m0) = h1' in Pair ((multA a a0), (mult_mon n m m0))

(** val invTerm : ('a1 -> 'a1) -> nat -> 'a1 term -> 'a1 term **)

let invTerm invA _ = function
| Pair (a, m) -> Pair ((invA a), m)

(** val t1 : 'a1 -> nat -> 'a1 term **)

let t1 a1 n =
  Pair (a1, (m1 n))

(** val minusTerm :
    ('a1 -> 'a1 -> 'a1) -> nat -> 'a1 term -> 'a1 term -> 'a1 term **)

let minusTerm minusA _ h h' =
  let Pair (a, m) = h in let Pair (a0, _) = h' in Pair ((minusA a a0), m)

(** val eqT_dec : nat -> 'a1 term -> 'a1 term -> sumbool **)

let eqT_dec n x y =
  eqmon_dec n (t2M n x) (t2M n y)

(** val ltT_dec :
    nat -> (mon -> mon -> sumbool sumor) -> 'a1 term -> 'a1 term -> sumbool
    sumor **)

let ltT_dec n ltM_dec x y =
  ltM_dec (t2M n x) (t2M n y)

(** val pX : nat -> 'a1 term -> 'a1 term list -> 'a1 term list **)

let pX _ x x0 =
  Cons (x, x0)

(** val pO : nat -> 'a1 term list **)

let pO _ =
  Nil

type 'a poly = 'a term list

(** val projsig1 : 'a1 -> 'a1 **)

let projsig1 h =
  h

(** val plusp :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> sumbool) -> nat -> (mon ->
    mon -> sumbool sumor) -> ('a1 term list, 'a1 term list) prod -> 'a1 term
    list **)

let rec plusp a0 plusA eqA_dec n ltM_dec = function
| Pair (l0, l1) ->
  (match l0 with
   | Nil -> l1
   | Cons (t, l2) ->
     (match l1 with
      | Nil -> pX n t l2
      | Cons (t0, l3) ->
        (match ltT_dec n ltM_dec t t0 with
         | Inleft s ->
           (match s with
            | Left ->
              let rec0 =
                plusp a0 plusA eqA_dec n ltM_dec (Pair ((pX n t l2), l3))
              in
              pX n t0 rec0
            | Right ->
              let rec0 =
                plusp a0 plusA eqA_dec n ltM_dec (Pair (l2, (pX n t0 l3)))
              in
              pX n t rec0)
         | Inright ->
           letP (plusTerm plusA n t t0) (fun letA _ ->
             match zeroP_dec a0 eqA_dec n letA with
             | Left -> plusp a0 plusA eqA_dec n ltM_dec (Pair (l2, l3))
             | Right ->
               let rec0 = plusp a0 plusA eqA_dec n ltM_dec (Pair (l2, l3)) in
               pX n letA rec0))))

(** val pluspf :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> sumbool) -> nat -> (mon ->
    mon -> sumbool sumor) -> 'a1 term list -> 'a1 term list -> 'a1 term list **)

let pluspf a0 plusA eqA_dec n ltM_dec l1 l2 =
  projsig1 (plusp a0 plusA eqA_dec n ltM_dec (Pair (l1, l2)))

(** val splus :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> ('a1 -> 'a1 ->
    sumbool) -> nat -> (mon -> mon -> sumbool sumor) -> 'a1 poly -> 'a1 poly
    -> 'a1 poly **)

let splus a0 _ plusA _ _ _ _ eqA_dec n ltM_dec sp2 sp3 =
  pluspf a0 plusA eqA_dec n ltM_dec sp3 sp2

(** val mults :
    ('a1 -> 'a1 -> 'a1) -> nat -> 'a1 term -> 'a1 term list -> 'a1 term list **)

let rec mults multA n a = function
| Nil -> pO n
| Cons (y, l) -> pX n (multTerm multA n a y) (mults multA n a l)

(** val tmults :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> sumbool) -> nat -> 'a1 term
    -> 'a1 term list -> 'a1 term list **)

let tmults a0 multA eqA_dec n a h' =
  match zeroP_dec a0 eqA_dec n a with
  | Left -> pO n
  | Right -> mults multA n a h'

(** val minuspp :
    'a1 -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> sumbool) -> nat -> (mon -> mon -> sumbool sumor) ->
    ('a1 term list, 'a1 term list) prod -> 'a1 term list **)

let rec minuspp a0 a1 invA minusA multA eqA_dec n ltM_dec = function
| Pair (l0, l1) ->
  (match l0 with
   | Nil -> mults multA n (invTerm invA n (t1 a1 n)) l1
   | Cons (t, l2) ->
     (match l1 with
      | Nil -> pX n t l2
      | Cons (t0, l3) ->
        (match ltT_dec n ltM_dec t t0 with
         | Inleft s ->
           (match s with
            | Left ->
              let rec0 =
                minuspp a0 a1 invA minusA multA eqA_dec n ltM_dec (Pair
                  ((pX n t l2), l3))
              in
              pX n (invTerm invA n t0) rec0
            | Right ->
              let rec0 =
                minuspp a0 a1 invA minusA multA eqA_dec n ltM_dec (Pair (l2,
                  (pX n t0 l3)))
              in
              pX n t rec0)
         | Inright ->
           let rec0 =
             minuspp a0 a1 invA minusA multA eqA_dec n ltM_dec (Pair (l2, l3))
           in
           letP (minusTerm minusA n t t0) (fun u _ ->
             match zeroP_dec a0 eqA_dec n u with
             | Left -> rec0
             | Right -> pX n u rec0))))

(** val minuspf :
    'a1 -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> sumbool) -> nat -> (mon -> mon -> sumbool sumor) -> 'a1
    term list -> 'a1 term list -> 'a1 term list **)

let minuspf a0 a1 invA minusA multA eqA_dec n ltM_dec l1 l2 =
  projsig1 (minuspp a0 a1 invA minusA multA eqA_dec n ltM_dec (Pair (l1, l2)))

(** val divTerm :
    'a1 -> ('a1 -> 'a1 -> __ -> 'a1) -> nat -> 'a1 term -> 'a1 term -> 'a1
    term **)

let divTerm _ divA n h b =
  let Pair (a, m) = h in
  let Pair (a0, m0) = b in Pair ((divA a a0 __), (div_mon n m m0))

(** val mk_clean : nat -> mon -> mon -> (mon, bool) prod **)

let mk_clean =
  div_mon_clean

(** val divTerm_dec :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> nat -> 'a1 term ->
    'a1 term -> sumbool **)

let divTerm_dec _ _ _ _ _ _ _ n a b =
  let Pair (_, m) = a in
  let Pair (_, m0) = b in
  let Pair (_, b0) = mk_clean n m m0 in
  (match b0 with
   | True -> Left
   | False -> Right)

(** val ppc : 'a1 -> nat -> 'a1 term -> 'a1 term -> 'a1 term **)

let ppc a1 n h h' =
  let Pair (_, m) = h in let Pair (_, m0) = h' in Pair (a1, (ppcm_mon n m m0))

(** val divP_dec :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> nat -> 'a1 term ->
    'a1 term -> sumbool **)

let divP_dec =
  divTerm_dec

(** val spminusf :
    'a1 -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> __ -> 'a1) -> ('a1 -> 'a1 -> sumbool) -> nat -> (mon ->
    mon -> sumbool sumor) -> 'a1 term -> 'a1 term -> 'a1 term list -> 'a1
    term list -> 'a1 term list **)

let spminusf a0 a1 invA minusA multA divA eqA_dec n ltM_dec a b p q =
  minuspf a0 a1 invA minusA multA eqA_dec n ltM_dec p
    (mults multA n (divTerm a0 divA n a b) q)

(** val mks : 'a1 -> nat -> 'a1 term list -> 'a1 poly **)

let mks _ _ p =
  p

(** val selectdivf :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> ('a1 -> 'a1 ->
    sumbool) -> nat -> 'a1 term -> 'a1 poly list -> 'a1 term list sumor **)

let rec selectdivf a0 a1 plusA invA minusA multA divA eqA_dec n a = function
| Nil -> Inright
| Cons (y, l) ->
  let h' = selectdivf a0 a1 plusA invA minusA multA divA eqA_dec n a l in
  (match y with
   | Nil -> h'
   | Cons (t, l0) ->
     (match divP_dec a0 a1 plusA invA minusA multA divA n a t with
      | Left -> Inleft (pX n t l0)
      | Right -> h'))

(** val reducef :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> ('a1 -> 'a1 ->
    sumbool) -> nat -> (mon -> mon -> sumbool sumor) -> 'a1 poly list -> 'a1
    poly -> 'a1 poly **)

let rec reducef a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec q = function
| Nil -> mks a0 n (pO n)
| Cons (t, l) ->
  let h'1 = selectdivf a0 a1 plusA invA minusA multA divA eqA_dec n t in
  (match h'1 q with
   | Inleft s ->
     (match s with
      | Nil -> assert false (* absurd case *)
      | Cons (t0, l0) ->
        reducef a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec q
          (mks a0 n
            (spminusf a0 a1 invA minusA multA divA eqA_dec n ltM_dec t t0 l
              l0)))
   | Inright ->
     let h'3 =
       reducef a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec q
         (mks a0 n l)
     in
     mks a0 n (pX n t h'3))

(** val spolyf :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> ('a1 -> 'a1 ->
    sumbool) -> nat -> (mon -> mon -> sumbool sumor) -> 'a1 term list -> 'a1
    term list -> 'a1 term list **)

let spolyf a0 a1 _ invA minusA multA divA eqA_dec n ltM_dec p q =
  match p with
  | Nil -> pO n
  | Cons (t, l) ->
    (match q with
     | Nil -> pO n
     | Cons (t0, l0) ->
       letP (ppc a1 n t t0) (fun u _ ->
         minuspf a0 a1 invA minusA multA eqA_dec n ltM_dec
           (mults multA n (divTerm a0 divA n u t) l)
           (mults multA n (divTerm a0 divA n u t0) l0)))

(** val multpf :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
    sumbool) -> nat -> (mon -> mon -> sumbool sumor) -> 'a1 term list -> 'a1
    term list -> 'a1 term list **)

let rec multpf a0 plusA multA eqA_dec n ltM_dec p q =
  match p with
  | Nil -> pO n
  | Cons (a, p') ->
    pluspf a0 plusA eqA_dec n ltM_dec (mults multA n a q)
      (multpf a0 plusA multA eqA_dec n ltM_dec p' q)

(** val smult :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> ('a1 -> 'a1 ->
    sumbool) -> nat -> (mon -> mon -> sumbool sumor) -> 'a1 poly -> 'a1 poly
    -> 'a1 poly **)

let smult a0 _ plusA _ _ multA _ eqA_dec n ltM_dec sp2 sp3 =
  multpf a0 plusA multA eqA_dec n ltM_dec sp3 sp2

(** val addEnd : 'a1 -> nat -> 'a1 poly -> 'a1 poly list -> 'a1 poly list **)

let rec addEnd a0 n a = function
| Nil -> Cons (a, Nil)
| Cons (y, l) -> Cons (y, (addEnd a0 n a l))

(** val spolyp :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> ('a1 -> 'a1 ->
    sumbool) -> nat -> (mon -> mon -> sumbool sumor) -> 'a1 poly -> 'a1 poly
    -> 'a1 poly **)

let spolyp a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec p q =
  spolyf a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec q p

(** val spO : 'a1 -> nat -> 'a1 poly **)

let spO _ =
  pO

(** val sp1 :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> nat -> 'a1 poly **)

let sp1 _ a1 _ _ _ _ _ n =
  pX n (Pair (a1, (m1 n))) Nil

(** val sgen :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> nat -> nat -> 'a1
    poly **)

let sgen _ a1 _ _ _ _ _ n m =
  pX n (Pair (a1, (gen_mon n m))) (pO n)

(** val sscal :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> ('a1 -> 'a1 ->
    sumbool) -> nat -> (mon -> mon -> sumbool sumor) -> 'a1 -> 'a1 poly ->
    'a1 poly **)

let sscal a0 _ _ _ _ multA _ eqA_dec n _ a p =
  tmults a0 multA eqA_dec n (Pair (a, (m1 n))) p

(** val zerop_dec : 'a1 -> nat -> 'a1 poly -> sumbool **)

let zerop_dec _ _ = function
| Nil -> Left
| Cons (_, _) -> Right

(** val divp_dec :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> ('a1 -> 'a1 ->
    sumbool) -> nat -> 'a1 poly -> 'a1 poly -> sumbool **)

let divp_dec a0 a1 plusA invA minusA multA divA _ n a = function
| Nil -> Right
| Cons (t, _) ->
  (match a with
   | Nil -> Right
   | Cons (t0, _) -> divP_dec a0 a1 plusA invA minusA multA divA n t0 t)

(** val ppcp :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> ('a1 -> 'a1 ->
    sumbool) -> nat -> 'a1 poly -> 'a1 poly -> 'a1 poly **)

let ppcp _ a1 _ _ _ _ _ _ n h' h'1 =
  match h' with
  | Nil -> pO n
  | Cons (t, _) ->
    (match h'1 with
     | Nil -> pO n
     | Cons (t0, _) -> Cons ((ppc a1 n t t0), (pO n)))

(** val unit0 :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> ('a1 -> 'a1 ->
    sumbool) -> nat -> 'a1 poly -> 'a1 term **)

let unit0 _ a1 _ _ _ _ divA _ n = function
| Nil -> t1 a1 n
| Cons (t, _) -> let Pair (a, _) = t in Pair ((divA a1 a __), (m1 n))

(** val nf :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> ('a1 -> 'a1 ->
    sumbool) -> nat -> (mon -> mon -> sumbool sumor) -> 'a1 poly -> 'a1 poly
    list -> 'a1 poly **)

let nf a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec p l =
  letP (reducef a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec l p)
    (fun u _ ->
    mults multA n
      (unit0 a0 a1 plusA invA minusA multA divA eqA_dec n (mks a0 n u)) u)

(** val foreigner_dec :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> nat -> 'a1 poly -> 'a1 poly ->
    sumbool **)

let foreigner_dec _ a1 multA n a = function
| Nil -> Left
| Cons (t, _) ->
  (match a with
   | Nil -> Left
   | Cons (t0, _) -> eqT_dec n (ppc a1 n t t0) (multTerm multA n t t0))

type 'a cpRes =
| Keep of 'a poly list
| DontKeep of 'a poly list

(** val addRes : 'a1 -> nat -> 'a1 poly -> 'a1 cpRes -> 'a1 cpRes **)

let addRes _ _ i = function
| Keep p -> Keep (Cons (i, p))
| DontKeep p -> DontKeep (Cons (i, p))

(** val slice :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> ('a1 -> 'a1 ->
    sumbool) -> nat -> 'a1 poly -> 'a1 poly -> 'a1 poly list -> 'a1 cpRes **)

let rec slice a0 a1 plusA invA minusA multA divA eqA_dec n i a = function
| Nil ->
  (match foreigner_dec a0 a1 multA n i a with
   | Left -> DontKeep Nil
   | Right -> Keep Nil)
| Cons (y, l) ->
  (match divp_dec a0 a1 plusA invA minusA multA divA eqA_dec n
           (ppcp a0 a1 plusA invA minusA multA divA eqA_dec n i a) y with
   | Left -> DontKeep (Cons (y, l))
   | Right ->
     (match divp_dec a0 a1 plusA invA minusA multA divA eqA_dec n
              (ppcp a0 a1 plusA invA minusA multA divA eqA_dec n i y) a with
      | Left -> slice a0 a1 plusA invA minusA multA divA eqA_dec n i a l
      | Right ->
        addRes a0 n y
          (slice a0 a1 plusA invA minusA multA divA eqA_dec n i a l)))

(** val genPcPf0 :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> ('a1 -> 'a1 ->
    sumbool) -> nat -> (mon -> mon -> sumbool sumor) -> 'a1 poly -> 'a1 poly
    list -> 'a1 poly list -> 'a1 poly list **)

let rec genPcPf0 a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec i aP r =
  match aP with
  | Nil -> r
  | Cons (p, l) ->
    (match slice a0 a1 plusA invA minusA multA divA eqA_dec n i p l with
     | Keep p0 ->
       let h'1 =
         genPcPf0 a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec i p0
       in
       addEnd a0 n
         (spolyp a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec i p)
         (h'1 r)
     | DontKeep p0 ->
       genPcPf0 a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec i p0 r)

(** val genPcPf :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> ('a1 -> 'a1 ->
    sumbool) -> nat -> (mon -> mon -> sumbool sumor) -> 'a1 poly -> 'a1 poly
    list -> 'a1 poly list -> 'a1 poly list **)

let genPcPf =
  genPcPf0

(** val genOCPf :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> ('a1 -> 'a1 ->
    sumbool) -> nat -> (mon -> mon -> sumbool sumor) -> 'a1 poly list -> 'a1
    poly list **)

let rec genOCPf a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec = function
| Nil -> Nil
| Cons (y, l) ->
  genPcPf a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec y l
    (genOCPf a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec l)

(** val pbuchf :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> ('a1 -> 'a1 ->
    sumbool) -> nat -> (mon -> mon -> sumbool sumor) -> ('a1 poly list, 'a1
    poly list) prod -> 'a1 poly list **)

let rec pbuchf a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec = function
| Pair (a, b) ->
  (match b with
   | Nil -> a
   | Cons (p, l) ->
     letP (nf a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec p a)
       (fun a2 _ ->
       match zerop_dec a0 n a2 with
       | Left ->
         pbuchf a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec (Pair
           (a, l))
       | Right ->
         pbuchf a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec (Pair
           ((addEnd a0 n a2 a),
           (genPcPf a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec a2 a
             l)))))

(** val strip : 'a1 -> nat -> 'a1 poly list -> 'a1 poly list **)

let strip _ _ h' =
  h'

(** val buch :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> ('a1 -> 'a1 ->
    sumbool) -> nat -> (mon -> mon -> sumbool sumor) -> 'a1 poly list -> 'a1
    poly list **)

let buch a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec p =
  strip a0 n
    (pbuchf a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec (Pair (p,
      (genOCPf a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec p))))

(** val redacc :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> ('a1 -> 'a1 ->
    sumbool) -> nat -> (mon -> mon -> sumbool sumor) -> 'a1 poly list -> 'a1
    poly list -> 'a1 poly list **)

let rec redacc a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec h' l =
  match h' with
  | Nil -> Nil
  | Cons (y, l0) ->
    letP
      (nf a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec y (app l0 l))
      (fun u _ ->
      match zerop_dec a0 n u with
      | Left ->
        redacc a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec l0 l
      | Right ->
        Cons (u,
          (redacc a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec l0
            (Cons (u, l)))))

(** val red :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> ('a1 -> 'a1 ->
    sumbool) -> nat -> (mon -> mon -> sumbool sumor) -> 'a1 poly list -> 'a1
    poly list **)

let red a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec l =
  redacc a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec l Nil

(** val redbuch :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1)
    -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> __ -> 'a1) -> ('a1 -> 'a1 ->
    sumbool) -> nat -> (mon -> mon -> sumbool sumor) -> 'a1 poly list -> 'a1
    poly list **)

let redbuch a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec l =
  red a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec
    (buch a0 a1 plusA invA minusA multA divA eqA_dec n ltM_dec l);;

(***********************************************************************)
(* Here is a small example file that uses the zarith library           *)
(* to compute some basis                                               *)
(***********************************************************************)

#use "topfind";;
#require "zarith.top";;

let var_list = ["a"; "b"; "c"; "d"; "e"; "f"];;

let rec int_of_nat = function 
| O -> 0 
| S m -> (1 + int_of_nat m);;

let string_of_nat n = string_of_int (int_of_nat n);;

let rec string_of_mon_rec l = function
| N_0 -> ""
| C_n (_, O, v) -> string_of_mon_rec (List.tl l) v
| C_n (_, S O, v) -> List.hd l ^ string_of_mon_rec (List.tl l) v
| C_n (_, k, v) -> List.hd l ^ "^" ^ string_of_nat k ^ string_of_mon_rec (List.tl l) v
;;

let rec is_null_mon = function
| N_0 -> true
| C_n (_, O, v) -> is_null_mon v
| C_n (_, k, v) -> false
;;

let string_of_mon m = string_of_mon_rec var_list m;;

type r6 =  (Q.t, mon) prod list;;

let string_of_qpair r m = if Q.equal r Q.one && (not (is_null_mon m)) then 
  string_of_mon m else Q.to_string r ^ " " ^ string_of_mon m

let rec string_of_r6 = function
| Nil -> ""
| Cons (Pair (r, m), Nil) -> string_of_qpair r m 
| Cons (Pair (r, m), p) -> 
     string_of_qpair r m ^ " + " ^ string_of_r6 p
;;

let rec n_to_p n  =  if n = 0 then O else (S (n_to_p (n-1)));;

let eqd n m = if (Q.equal n m) then  Left else Right;;

let ri = Q.of_int;;

let plusP: int -> r6 -> r6 -> r6 =  
    fun n -> 
     let n = n_to_p n in 
     (splus (ri 0) (ri 1) (Q.add) (Q.sub) (Q.neg) (Q.mul)
         (Q.div) eqd n (total_orderc_dec n));;

let multP: int -> r6 -> r6 -> r6  = 
  fun n -> 
   let n = n_to_p n in 
  (smult (ri 0) (ri 1) (Q.add) (Q.sub) (Q.neg) (Q.mul)
         (Q.div) eqd n (total_orderc_dec n));;

let scalP: int -> int -> r6 -> r6  = 
  fun n -> 
   let n = n_to_p n in 
      fun m -> 
      (sscal (ri 0) (ri 1) (Q.add) (Q.sub) (Q.neg) (Q.mul)
         (Q.div) eqd n (total_orderc_dec n) (ri m));;

let spO a0 n =  Nil;;

let p0 : int -> r6 = fun n -> (spO  (ri 0) (n_to_p n));;

let p1 : int -> r6 = (fun n -> (sp1 (ri 0) (ri 1) (Q.add) (Q.sub) (Q.neg) (Q.mul)
         (Q.div) (n_to_p n) )) ;;

let mon : int -> int -> r6 = fun n -> fun m -> sgen (ri 0) (ri 1) (Q.add) (Q.sub) (Q.neg) (Q.mul)
         (Q.div) (n_to_p n)  (n_to_p m);;

let div1 a b c = Q.div a b;;
 
let tbuch : int -> r6 list -> r6 list =
    (fun n ->
      let n = n_to_p n in 
      redbuch (ri 0) (ri 1) (Q.add) (Q.neg) (Q.sub) (Q.mul)
         (div1) eqd  n  (total_orderc_dec n));;

let rec l2l l = match l with [] -> Nil | (a::tl) -> Cons (a, l2l tl);;
let rec l5l l = match l with Nil -> [] | Cons (a,tl) -> a :: (l5l tl);;

let tbuchl = fun n -> fun l -> (l5l (tbuch n (l2l l)));;

let dim = 6;;
let plus = plusP dim;;
let mult = multP dim;;
let scal = scalP dim;;
let p1 = p1 dim;;
let gen = mon dim;;
let tbuch = tbuchl dim;;

let a = gen 0;;
let b = gen 1;;
let c = gen 2;;
let p1 =  gen 6;;

let r0 = (plus a (plus b c));;
let r1 = (plus (mult a b) (plus (mult b c) (mult c a)));;
let r2 = (plus (mult a (mult b c)) (scal (-1) p1));;

let print_lpol l = 
  List.map (fun n -> print_string (string_of_r6 n); print_newline()) l; ();;

let _ =
(print_string "3"; print_newline();
 print_string "init"; print_newline();
 print_lpol [r2;r1;r0];
 print_string "result"; print_newline();
 print_lpol (tbuch [r2;r1;r0]))
;;

let d = gen 3;;

let r0 = (plus a (plus b (plus c d)));;
let r1 = (plus (mult a b) (plus (mult b c) (plus (mult c d) (mult d a))));;
let r2 = (plus (mult a (mult b c)) (plus (mult b (mult c d)) (plus (mult c (mult d a)) 
             (mult d (mult a b)))));;
let r3 = (plus (mult a (mult b (mult c d))) (scal (-1) p1));;

let _ =
 print_string "4"; print_newline();
 print_string "init"; print_newline();
 print_lpol [r3;r2;r1;r0]; print_newline();
 print_string "result"; print_newline();
 print_lpol (tbuch [r3;r2;r1;r0])
;;

let e = gen 4;;

let r0 = (plus a (plus b (plus c (plus d e))));;
let r1 = (plus (mult a b) (plus (mult b c) (plus (mult c d) (plus (mult d e) (mult e a)))));;
let r2 = (plus (mult a (mult b c)) (plus (mult b (mult c d)) (plus (mult c (mult d e))
(plus (mult d (mult e a))
             (mult e(mult a b))))));;
let r3= (plus (mult a (mult b (mult c d))) (plus (mult b (mult c (mult d e))) 
(plus (mult c (mult d (mult e a)))
(plus (mult d (mult e (mult a b)))
             (mult e(mult a (mult b c)))))));;
let r4 = (plus (mult a (mult b (mult c (mult d e)))) (scal (-1) p1));;

let _ = 
  print_string "5"; print_newline();
  print_string "init"; print_newline();
  print_lpol [r4;r3;r2;r1;r0];
  print_string "result"; print_newline();
  print_lpol (tbuch [r4; r3;r2;r1;r0])
;;

let f = gen 5;;

let r0 = (plus a (plus b (plus c (plus d (plus e f)))));;
let r1 = (plus (mult a b) (plus (mult b c) (plus (mult c d) (plus (mult d e) (plus (mult e f) (mult f a))))));;
let r2 = (plus (mult a (mult b c)) (plus (mult b (mult c d)) (plus (mult c (mult d e))
(plus (mult d (mult e f))
(plus (mult e (mult f a))
             (mult f (mult a b)))))));;
let r3= (plus (mult a (mult b (mult c d))) (plus (mult b (mult c (mult d e))) 
(plus (mult c (mult d (mult e f)))
(plus (mult d (mult e (mult f a)))
(plus (mult e (mult f (mult a b)))
             (mult f(mult a (mult b c))))))));;
let r4= (plus (mult a (mult b (mult c (mult d e)))) (plus (mult b (mult c (mult d (mult e f)))) 
(plus (mult c (mult d (mult e (mult f a))))
(plus (mult d (mult e (mult f (mult a b))))
(plus (mult e (mult f (mult a (mult b c))))
             (mult f(mult a (mult b (mult c d)))))))));;
let r5 = (plus (mult a (mult b (mult c (mult d (mult e f))))) (scal (-1) p1));;

let () =
 print_string "6"; print_newline();
 print_string "init"; print_newline();
 print_lpol [r5;r4;r3;r2;r1;r0];
 print_string "result"; print_newline();
 print_lpol (tbuch [r5;r4; r3;r2;r1;r0]);
;;
