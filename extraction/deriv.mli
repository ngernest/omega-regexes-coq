
type __ = Obj.t

type nat =
| O
| S of nat

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

val compareSpec2Type : comparison -> compareSpecT

type 'a compSpecT = compareSpecT

val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



module Nat :
 sig
  val compare : nat -> nat -> comparison

  val max : nat -> nat -> nat

  val eq_dec : nat -> nat -> bool

  module Private_Dec :
   sig
    val max_case_strong :
      nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1

    val max_case :
      nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val max_dec : nat -> nat -> bool
   end

  val max_dec : nat -> nat -> bool
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

type 'a addOp = 'a -> 'a -> 'a

val add_op_ : 'a1 addOp -> 'a1 -> 'a1 -> 'a1

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

val esum_add : 'a1 regexpr addOp

type 'a omega_regexpr =
| OEzero
| OEsum of 'a omega_regexpr * 'a omega_regexpr
| OEcat of 'a regexpr * 'a omega_regexpr
| OEomega of 'a regexpr

val regexpr_equ : 'a1 equ -> 'a1 regexpr equ

val regexpr_equ_dec : 'a1 equDec -> 'a1 regexpr equDec

val omega_regexpr_equ : 'a1 equ -> 'a1 omega_regexpr equ

val omega_regexpr_equ_dec : 'a1 equDec -> 'a1 omega_regexpr equDec

type 'a coword = 'a __coword Lazy.t
and 'a __coword =
| Lcons of 'a * 'a coword

val mk_dot_reg : 'a1 equ -> 'a1 regexpr -> 'a1 regexpr -> 'a1 regexpr

val mk_plus_reg : 'a1 equDec -> 'a1 regexpr -> 'a1 regexpr -> 'a1 regexpr

val mk_dot : 'a1 equ -> 'a1 regexpr -> 'a1 omega_regexpr -> 'a1 omega_regexpr

val mk_plus :
  'a1 equDec -> 'a1 omega_regexpr -> 'a1 omega_regexpr -> 'a1 omega_regexpr

val final : 'a1 regexpr -> bool

val compute_regular_deriv : 'a1 equDec -> 'a1 -> 'a1 regexpr -> 'a1 regexpr

val compute_deriv :
  'a1 equDec -> 'a1 -> 'a1 omega_regexpr -> 'a1 omega_regexpr

type 'a finite =
  'a list
  (* singleton inductive, whose constructor was Build_Finite *)

val all_elem : 'a1 equ -> 'a1 finite -> 'a1 list

val non_zero_regexp : 'a1 regexpr -> bool

val collect_alphabet_reg : 'a1 regexpr -> 'a1 list

val non_zero_omega_regexp : 'a1 omega_regexpr -> bool

val collect_alphabet : 'a1 omega_regexpr -> 'a1 list

val unequal_alphabet :
  'a1 equDec -> 'a1 omega_regexpr -> 'a1 omega_regexpr -> bool

val trivially_not_equal :
  'a1 equDec -> 'a1 equ -> 'a1 finite -> 'a1 omega_regexpr -> 'a1
  omega_regexpr -> bool

type 'a listEquations = ('a omega_regexpr * 'a omega_regexpr) list

type 'a algo_option =
| FINISHED
| CLASH of 'a
| CONTINUE of 'a

val algo_step :
  'a1 equDec -> 'a1 equ -> 'a1 finite -> 'a1 listEquations -> 'a1
  listEquations

val run_algo :
  'a1 equDec -> 'a1 equ -> 'a1 finite -> 'a1 listEquations -> 'a1
  listEquations coword

val observe :
  'a1 equDec -> 'a1 finite -> 'a1 listEquations coword -> 'a1 listEquations
  algo_option coword

type 'a res_opt =
| EQUAL
| NOT_EQUAL of 'a
| DONT_KNOW of 'a

val find_res : 'a1 algo_option coword -> nat -> 'a1 res_opt

val bounded_check :
  'a1 equDec -> 'a1 finite -> 'a1 omega_regexpr -> 'a1 omega_regexpr -> nat
  -> 'a1 listEquations res_opt

val nat_fin_equ : nat -> nat equ

val nat_fin_equ_dec : nat -> nat equDec

val seq_wit_aux : nat -> nat -> nat list

val seq_wit : nat -> nat list

val nat_fin : nat -> nat finite

val max_num_reg_expr : nat regexpr -> nat

val max_num_omega_reg_expr : nat omega_regexpr -> nat

val max_num_expr : nat omega_regexpr -> nat omega_regexpr -> nat

type bound =
| Bound_Ezero
| Bound_Eone
| Bound_Char of nat
| Bound_Esum of nat regexpr * nat regexpr * bound * bound
| Bound_Ecat of nat regexpr * nat regexpr * bound * bound
| Bound_Estar of nat regexpr * bound

val bound_le : nat regexpr -> nat -> nat -> bound -> bound

val compute_bound_correct : nat regexpr -> bound

val convert_reg : nat -> nat regexpr -> bound -> nat regexpr

type bound_Omega =
| Bound_OEzero
| Bound_OEsum of nat omega_regexpr * nat omega_regexpr * bound_Omega
   * bound_Omega
| Bound_OEcat of nat regexpr * nat omega_regexpr * bound * bound_Omega
| Bound_OEomega of nat regexpr * bound

val bound_omega_le :
  nat omega_regexpr -> nat -> nat -> bound_Omega -> bound_Omega

val compute_bound_omega_correct : nat omega_regexpr -> bound_Omega

val convert_omega_reg :
  nat -> nat omega_regexpr -> bound_Omega -> nat omega_regexpr

val convert_obligation_1 :
  nat omega_regexpr -> nat omega_regexpr -> bound_Omega

val convert_obligation_2 :
  nat omega_regexpr -> nat omega_regexpr -> bound_Omega

val convert :
  nat omega_regexpr -> nat omega_regexpr -> nat omega_regexpr * nat
  omega_regexpr

val check :
  nat omega_regexpr -> nat omega_regexpr -> nat listEquations res_opt
