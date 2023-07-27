
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type nat =
| O
| S of nat

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type _ _ =
  compareSpec2Type

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



module Nat =
 struct
  (** val compare : nat -> nat -> comparison **)

  let rec compare n m =
    match n with
    | O -> (match m with
            | O -> Eq
            | S _ -> Lt)
    | S n' -> (match m with
               | O -> Gt
               | S m' -> compare n' m')

  (** val max : nat -> nat -> nat **)

  let rec max n m =
    match n with
    | O -> m
    | S n' -> (match m with
               | O -> n
               | S m' -> S (max n' m'))

  (** val eq_dec : nat -> nat -> bool **)

  let rec eq_dec n m =
    match n with
    | O -> (match m with
            | O -> true
            | S _ -> false)
    | S n0 -> (match m with
               | O -> false
               | S n1 -> eq_dec n0 n1)

  module Private_Dec =
   struct
    (** val max_case_strong :
        nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__
        -> 'a1) -> 'a1 **)

    let max_case_strong n m compat hl hr =
      let c = compSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat n (max n m) __ (hl __)
       | _ -> compat m (max n m) __ (hr __))

    (** val max_case :
        nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let max_case n m x x0 x1 =
      max_case_strong n m x (fun _ -> x0) (fun _ -> x1)

    (** val max_dec : nat -> nat -> bool **)

    let max_dec n m =
      max_case n m (fun _ _ _ h0 -> h0) true false
   end

  (** val max_dec : nat -> nat -> bool **)

  let max_dec =
    Private_Dec.max_dec
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a :: l0 -> (||) (f a) (existsb f l0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l0 -> (&&) (f a) (forallb f l0)

type 'a addOp = 'a -> 'a -> 'a

(** val add_op_ : 'a1 addOp -> 'a1 -> 'a1 -> 'a1 **)

let add_op_ addOp0 =
  addOp0

type 'a equ =
| Build_Equ

type 'a equDec = { equ_dec_equ : 'a equ; equ_dec : ('a -> 'a -> bool) }

type 'a regexpr =
| Ezero
| Eone
| Echar of 'a
| Esum of 'a regexpr * 'a regexpr
| Ecat of 'a regexpr * 'a regexpr
| Estar of 'a regexpr

(** val esum_add : 'a1 regexpr addOp **)

let esum_add x x0 =
  Esum (x, x0)

type 'a omega_regexpr =
| OEzero
| OEsum of 'a omega_regexpr * 'a omega_regexpr
| OEcat of 'a regexpr * 'a omega_regexpr
| OEomega of 'a regexpr

(** val regexpr_equ : 'a1 equ -> 'a1 regexpr equ **)

let regexpr_equ _ =
  Build_Equ

(** val regexpr_equ_dec : 'a1 equDec -> 'a1 regexpr equDec **)

let regexpr_equ_dec h =
  { equ_dec_equ = (regexpr_equ h.equ_dec_equ); equ_dec = (fun x y ->
    let rec f r y0 =
      match r with
      | Ezero -> (match y0 with
                  | Ezero -> true
                  | _ -> false)
      | Eone -> (match y0 with
                 | Eone -> true
                 | _ -> false)
      | Echar a -> (match y0 with
                    | Echar a0 -> h.equ_dec a a0
                    | _ -> false)
      | Esum (r1, r2) ->
        (match y0 with
         | Esum (r3, r4) -> let s = f r1 r3 in if s then f r2 r4 else false
         | _ -> false)
      | Ecat (r1, r2) ->
        (match y0 with
         | Ecat (r3, r4) -> let s = f r1 r3 in if s then f r2 r4 else false
         | _ -> false)
      | Estar r0 -> (match y0 with
                     | Estar r1 -> f r0 r1
                     | _ -> false)
    in f x y) }

(** val omega_regexpr_equ : 'a1 equ -> 'a1 omega_regexpr equ **)

let omega_regexpr_equ _ =
  Build_Equ

(** val omega_regexpr_equ_dec : 'a1 equDec -> 'a1 omega_regexpr equDec **)

let omega_regexpr_equ_dec eQU =
  { equ_dec_equ = (omega_regexpr_equ eQU.equ_dec_equ); equ_dec = (fun x y ->
    let rec f o y0 =
      match o with
      | OEzero -> (match y0 with
                   | OEzero -> true
                   | _ -> false)
      | OEsum (e1, e2) ->
        (match y0 with
         | OEsum (e3, e4) -> let s = f e1 e3 in if s then f e2 e4 else false
         | _ -> false)
      | OEcat (r, e) ->
        (match y0 with
         | OEcat (r0, e0) ->
           let s = f e e0 in
           if s then (regexpr_equ_dec eQU).equ_dec r r0 else false
         | _ -> false)
      | OEomega r ->
        (match y0 with
         | OEomega r0 -> (regexpr_equ_dec eQU).equ_dec r r0
         | _ -> false)
    in f x y) }

type 'a coword = 'a __coword Lazy.t
and 'a __coword =
| Lcons of 'a * 'a coword

(** val mk_dot_reg : 'a1 equ -> 'a1 regexpr -> 'a1 regexpr -> 'a1 regexpr **)

let mk_dot_reg _ r1 r2 =
  match r1 with
  | Ezero -> Ezero
  | Eone -> (match r2 with
             | Ezero -> Ezero
             | _ -> r2)
  | _ -> (match r2 with
          | Ezero -> Ezero
          | Eone -> r1
          | _ -> Ecat (r1, r2))

(** val mk_plus_reg :
    'a1 equDec -> 'a1 regexpr -> 'a1 regexpr -> 'a1 regexpr **)

let mk_plus_reg h r1 r2 =
  match r1 with
  | Ezero -> r2
  | _ ->
    (match r2 with
     | Ezero -> r1
     | _ ->
       if (regexpr_equ_dec h).equ_dec r1 r2
       then r1
       else add_op_ esum_add r1 r2)

(** val mk_dot :
    'a1 equ -> 'a1 regexpr -> 'a1 omega_regexpr -> 'a1 omega_regexpr **)

let mk_dot _ r e =
  match r with
  | Ezero -> OEzero
  | Eone -> e
  | _ -> (match e with
          | OEzero -> OEzero
          | _ -> OEcat (r, e))

(** val mk_plus :
    'a1 equDec -> 'a1 omega_regexpr -> 'a1 omega_regexpr -> 'a1 omega_regexpr **)

let mk_plus h e1 e2 =
  match e1 with
  | OEzero -> e2
  | _ ->
    (match e2 with
     | OEzero -> e1
     | _ ->
       if (omega_regexpr_equ_dec h).equ_dec e1 e2 then e1 else OEsum (e1, e2))

(** val final : 'a1 regexpr -> bool **)

let rec final = function
| Ezero -> false
| Echar _ -> false
| Esum (e1, e2) -> (||) (final e1) (final e2)
| Ecat (e1, e2) -> (&&) (final e1) (final e2)
| _ -> true

(** val compute_regular_deriv :
    'a1 equDec -> 'a1 -> 'a1 regexpr -> 'a1 regexpr **)

let rec compute_regular_deriv h a = function
| Echar b -> if h.equ_dec a b then Eone else Ezero
| Esum (e1, e2) ->
  mk_plus_reg h (compute_regular_deriv h a e1) (compute_regular_deriv h a e2)
| Ecat (e1, e2) ->
  if final e1
  then mk_plus_reg h
         (mk_dot_reg h.equ_dec_equ (compute_regular_deriv h a e1) e2)
         (compute_regular_deriv h a e2)
  else mk_dot_reg h.equ_dec_equ (compute_regular_deriv h a e1) e2
| Estar e0 ->
  mk_dot_reg h.equ_dec_equ (compute_regular_deriv h a e0) (Estar e0)
| _ -> Ezero

(** val compute_deriv :
    'a1 equDec -> 'a1 -> 'a1 omega_regexpr -> 'a1 omega_regexpr **)

let rec compute_deriv h a = function
| OEzero -> OEzero
| OEsum (e_1, e_2) ->
  mk_plus h (compute_deriv h a e_1) (compute_deriv h a e_2)
| OEcat (e_1, e_2) ->
  if final e_1
  then mk_plus h (mk_dot h.equ_dec_equ (compute_regular_deriv h a e_1) e_2)
         (compute_deriv h a e_2)
  else mk_dot h.equ_dec_equ (compute_regular_deriv h a e_1) e_2
| OEomega e0 ->
  mk_dot h.equ_dec_equ (compute_regular_deriv h a e0) (OEomega e0)

type 'a finite =
  'a list
  (* singleton inductive, whose constructor was Build_Finite *)

(** val all_elem : 'a1 equ -> 'a1 finite -> 'a1 list **)

let all_elem _ finite0 =
  finite0

(** val non_zero_regexp : 'a1 regexpr -> bool **)

let rec non_zero_regexp = function
| Ezero -> false
| Esum (e1, e2) -> (||) (non_zero_regexp e1) (non_zero_regexp e2)
| Ecat (e1, e2) -> (&&) (non_zero_regexp e1) (non_zero_regexp e2)
| _ -> true

(** val collect_alphabet_reg : 'a1 regexpr -> 'a1 list **)

let rec collect_alphabet_reg = function
| Echar a -> a :: []
| Esum (e1, e2) -> app (collect_alphabet_reg e1) (collect_alphabet_reg e2)
| Ecat (e1, e2) ->
  if (&&) (non_zero_regexp e1) (non_zero_regexp e2)
  then app (collect_alphabet_reg e1) (collect_alphabet_reg e2)
  else []
| Estar e0 -> collect_alphabet_reg e0
| _ -> []

(** val non_zero_omega_regexp : 'a1 omega_regexpr -> bool **)

let rec non_zero_omega_regexp = function
| OEzero -> false
| OEsum (e1, e2) -> (||) (non_zero_omega_regexp e1) (non_zero_omega_regexp e2)
| OEcat (e1, e2) -> (&&) (non_zero_regexp e1) (non_zero_omega_regexp e2)
| OEomega e0 ->
  (match collect_alphabet_reg e0 with
   | [] -> false
   | _ :: _ -> true)

(** val collect_alphabet : 'a1 omega_regexpr -> 'a1 list **)

let rec collect_alphabet = function
| OEzero -> []
| OEsum (e1, e2) -> app (collect_alphabet e1) (collect_alphabet e2)
| OEcat (e1, e2) ->
  if (&&) (non_zero_regexp e1) (non_zero_omega_regexp e2)
  then app (collect_alphabet_reg e1) (collect_alphabet e2)
  else []
| OEomega e0 -> collect_alphabet_reg e0

(** val unequal_alphabet :
    'a1 equDec -> 'a1 omega_regexpr -> 'a1 omega_regexpr -> bool **)

let unequal_alphabet h e1 e2 =
  let l1 = collect_alphabet e1 in
  let l2 = collect_alphabet e2 in
  (||)
    (existsb (fun a ->
      forallb (fun b -> if h.equ_dec a b then false else true) l2) l1)
    (existsb (fun a ->
      forallb (fun b -> if h.equ_dec a b then false else true) l1) l2)

(** val trivially_not_equal :
    'a1 equDec -> 'a1 equ -> 'a1 finite -> 'a1 omega_regexpr -> 'a1
    omega_regexpr -> bool **)

let trivially_not_equal h _ _ e1 e2 =
  unequal_alphabet h e1 e2

type 'a listEquations = ('a omega_regexpr * 'a omega_regexpr) list

type 'a algo_option =
| FINISHED
| CLASH of 'a
| CONTINUE of 'a

(** val algo_step :
    'a1 equDec -> 'a1 equ -> 'a1 finite -> 'a1 listEquations -> 'a1
    listEquations **)

let algo_step h h0 h1 = function
| [] -> []
| p :: l' ->
  let (e1, e2) = p in
  if (omega_regexpr_equ_dec h).equ_dec e1 e2
  then l'
  else let d =
         map (fun a -> ((compute_deriv h a e1), (compute_deriv h a e2)))
           (all_elem h0 h1)
       in
       app l' d

(** val run_algo :
    'a1 equDec -> 'a1 equ -> 'a1 finite -> 'a1 listEquations -> 'a1
    listEquations coword **)

let rec run_algo h h0 h1 l =
  lazy (Lcons (l, (run_algo h h0 h1 (algo_step h h0 h1 l))))

(** val observe :
    'a1 equDec -> 'a1 finite -> 'a1 listEquations coword -> 'a1 listEquations
    algo_option coword **)

let rec observe dEC f s =
  let Lcons (l, s0) = Lazy.force s in
  let r =
    match l with
    | [] -> FINISHED
    | p :: _ ->
      let (e1, e2) = p in
      if trivially_not_equal dEC dEC.equ_dec_equ f e1 e2
      then CLASH ((e1, e2) :: [])
      else CONTINUE l
  in
  lazy (Lcons (r, (observe dEC f s0)))

type 'a res_opt =
| EQUAL
| NOT_EQUAL of 'a
| DONT_KNOW of 'a

(** val find_res : 'a1 algo_option coword -> nat -> 'a1 res_opt **)

let rec find_res w n =
  let Lcons (x, w') = Lazy.force w in
  (match x with
   | FINISHED -> EQUAL
   | CLASH l -> NOT_EQUAL l
   | CONTINUE l -> (match n with
                    | O -> DONT_KNOW l
                    | S n' -> find_res w' n'))

(** val bounded_check :
    'a1 equDec -> 'a1 finite -> 'a1 omega_regexpr -> 'a1 omega_regexpr -> nat
    -> 'a1 listEquations res_opt **)

let bounded_check dEC h e1 e2 n =
  find_res (observe dEC h (run_algo dEC dEC.equ_dec_equ h ((e1, e2) :: []))) n

(** val nat_fin_equ : nat -> nat equ **)

let nat_fin_equ _ =
  Build_Equ

(** val nat_fin_equ_dec : nat -> nat equDec **)

let nat_fin_equ_dec n =
  { equ_dec_equ = (nat_fin_equ n); equ_dec = Nat.eq_dec }

(** val seq_wit_aux : nat -> nat -> nat list **)

let rec seq_wit_aux n = function
| O -> []
| S i0 -> i0 :: (seq_wit_aux n i0)

(** val seq_wit : nat -> nat list **)

let seq_wit n =
  seq_wit_aux n n

(** val nat_fin : nat -> nat finite **)

let nat_fin =
  seq_wit

(** val max_num_reg_expr : nat regexpr -> nat **)

let rec max_num_reg_expr = function
| Echar i -> i
| Esum (e1, e2) -> Nat.max (max_num_reg_expr e1) (max_num_reg_expr e2)
| Ecat (e1, e2) -> Nat.max (max_num_reg_expr e1) (max_num_reg_expr e2)
| Estar e0 -> max_num_reg_expr e0
| _ -> O

(** val max_num_omega_reg_expr : nat omega_regexpr -> nat **)

let rec max_num_omega_reg_expr = function
| OEzero -> O
| OEsum (e1, e2) ->
  Nat.max (max_num_omega_reg_expr e1) (max_num_omega_reg_expr e2)
| OEcat (e1, e2) -> Nat.max (max_num_reg_expr e1) (max_num_omega_reg_expr e2)
| OEomega e0 -> max_num_reg_expr e0

(** val max_num_expr : nat omega_regexpr -> nat omega_regexpr -> nat **)

let max_num_expr e1 e2 =
  Nat.max (max_num_omega_reg_expr e1) (max_num_omega_reg_expr e2)

type bound =
| Bound_Ezero
| Bound_Eone
| Bound_Char of nat
| Bound_Esum of nat regexpr * nat regexpr * bound * bound
| Bound_Ecat of nat regexpr * nat regexpr * bound * bound
| Bound_Estar of nat regexpr * bound

(** val bound_le : nat regexpr -> nat -> nat -> bound -> bound **)

let rec bound_le e n m x =
  match e with
  | Ezero -> Bound_Ezero
  | Eone -> Bound_Eone
  | Echar a -> Bound_Char a
  | Esum (r1, r2) ->
    (match x with
     | Bound_Esum (_, _, h1, h2) ->
       Bound_Esum (r1, r2, (bound_le r1 n m h1), (bound_le r2 n m h2))
     | _ -> assert false (* absurd case *))
  | Ecat (r1, r2) ->
    (match x with
     | Bound_Ecat (_, _, h1, h2) ->
       Bound_Ecat (r1, r2, (bound_le r1 n m h1), (bound_le r2 n m h2))
     | _ -> assert false (* absurd case *))
  | Estar r ->
    Bound_Estar (r,
      (match x with
       | Bound_Estar (_, he) -> bound_le r n m he
       | _ -> assert false (* absurd case *)))

(** val compute_bound_correct : nat regexpr -> bound **)

let rec compute_bound_correct = function
| Ezero -> Bound_Ezero
| Eone -> Bound_Eone
| Echar a -> Bound_Char a
| Esum (r1, r2) ->
  let m = max_num_reg_expr r1 in
  let n = max_num_reg_expr r2 in
  let s = Nat.max_dec m n in
  if s
  then Bound_Esum (r1, r2, (compute_bound_correct r1),
         (bound_le r2 (S n) (S m) (compute_bound_correct r2)))
  else Bound_Esum (r1, r2,
         (bound_le r1 (S m) (S n) (compute_bound_correct r1)),
         (compute_bound_correct r2))
| Ecat (r1, r2) ->
  let m = max_num_reg_expr r1 in
  let n = max_num_reg_expr r2 in
  let s = Nat.max_dec m n in
  if s
  then Bound_Ecat (r1, r2, (compute_bound_correct r1),
         (bound_le r2 (S n) (S m) (compute_bound_correct r2)))
  else Bound_Ecat (r1, r2,
         (bound_le r1 (S m) (S n) (compute_bound_correct r1)),
         (compute_bound_correct r2))
| Estar r0 -> Bound_Estar (r0, (compute_bound_correct r0))

(** val convert_reg : nat -> nat regexpr -> bound -> nat regexpr **)

let rec convert_reg n _ = function
| Bound_Ezero -> Ezero
| Bound_Eone -> Eone
| Bound_Char i -> Echar i
| Bound_Esum (e1, e2, h1, h2) ->
  Esum ((convert_reg n e1 h1), (convert_reg n e2 h2))
| Bound_Ecat (e1, e2, h1, h2) ->
  Ecat ((convert_reg n e1 h1), (convert_reg n e2 h2))
| Bound_Estar (e, he) -> Estar (convert_reg n e he)

type bound_Omega =
| Bound_OEzero
| Bound_OEsum of nat omega_regexpr * nat omega_regexpr * bound_Omega
   * bound_Omega
| Bound_OEcat of nat regexpr * nat omega_regexpr * bound * bound_Omega
| Bound_OEomega of nat regexpr * bound

(** val bound_omega_le :
    nat omega_regexpr -> nat -> nat -> bound_Omega -> bound_Omega **)

let rec bound_omega_le e n m x =
  match e with
  | OEzero -> Bound_OEzero
  | OEsum (e1, e2) ->
    (match x with
     | Bound_OEsum (_, _, h1, h2) ->
       Bound_OEsum (e1, e2, (bound_omega_le e1 n m h1),
         (bound_omega_le e2 n m h2))
     | _ -> assert false (* absurd case *))
  | OEcat (r, e0) ->
    (match x with
     | Bound_OEcat (_, _, h1, h2) ->
       Bound_OEcat (r, e0, (bound_le r n m h1), (bound_omega_le e0 n m h2))
     | _ -> assert false (* absurd case *))
  | OEomega r ->
    (match x with
     | Bound_OEomega (_, he) -> Bound_OEomega (r, (bound_le r n m he))
     | _ -> assert false (* absurd case *))

(** val compute_bound_omega_correct : nat omega_regexpr -> bound_Omega **)

let rec compute_bound_omega_correct = function
| OEzero -> Bound_OEzero
| OEsum (e1, e2) ->
  let m = max_num_omega_reg_expr e1 in
  let n = max_num_omega_reg_expr e2 in
  let s = Nat.max_dec m n in
  if s
  then Bound_OEsum (e1, e2, (compute_bound_omega_correct e1),
         (bound_omega_le e2 (S n) (S m) (compute_bound_omega_correct e2)))
  else Bound_OEsum (e1, e2,
         (bound_omega_le e1 (S m) (S n) (compute_bound_omega_correct e1)),
         (compute_bound_omega_correct e2))
| OEcat (r, e) ->
  let m = max_num_reg_expr r in
  let n = max_num_omega_reg_expr e in
  let s = Nat.max_dec m n in
  if s
  then Bound_OEcat (r, e, (compute_bound_correct r),
         (bound_omega_le e (S n) (S m) (compute_bound_omega_correct e)))
  else Bound_OEcat (r, e, (bound_le r (S m) (S n) (compute_bound_correct r)),
         (compute_bound_omega_correct e))
| OEomega r -> Bound_OEomega (r, (compute_bound_correct r))

(** val convert_omega_reg :
    nat -> nat omega_regexpr -> bound_Omega -> nat omega_regexpr **)

let rec convert_omega_reg n _ = function
| Bound_OEzero -> OEzero
| Bound_OEsum (e1, e2, h1, h2) ->
  OEsum ((convert_omega_reg n e1 h1), (convert_omega_reg n e2 h2))
| Bound_OEcat (e1, e2, h1, h2) ->
  OEcat ((convert_reg n e1 h1), (convert_omega_reg n e2 h2))
| Bound_OEomega (e, he) -> OEomega (convert_reg n e he)

(** val convert_obligation_1 :
    nat omega_regexpr -> nat omega_regexpr -> bound_Omega **)

let convert_obligation_1 e1 e2 =
  bound_omega_le e1 (S (max_num_omega_reg_expr e1)) (S (max_num_expr e1 e2))
    (compute_bound_omega_correct e1)

(** val convert_obligation_2 :
    nat omega_regexpr -> nat omega_regexpr -> bound_Omega **)

let convert_obligation_2 e1 e2 =
  bound_omega_le e2 (S (max_num_omega_reg_expr e2)) (S (max_num_expr e1 e2))
    (compute_bound_omega_correct e2)

(** val convert :
    nat omega_regexpr -> nat omega_regexpr -> nat omega_regexpr * nat
    omega_regexpr **)

let convert e1 e2 =
  let m = S (max_num_expr e1 e2) in
  let e1' = convert_omega_reg m e1 (convert_obligation_1 e1 e2) in
  let e2' = convert_omega_reg m e2 (convert_obligation_2 e1 e2) in (e1', e2')

(** val check :
    nat omega_regexpr -> nat omega_regexpr -> nat listEquations res_opt **)

let check e1 e2 =
  let (e3, e4) = convert e1 e2 in
  bounded_check (nat_fin_equ_dec (S (max_num_expr e1 e2)))
    (nat_fin (S (max_num_expr e1 e2))) e3 e4 (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
