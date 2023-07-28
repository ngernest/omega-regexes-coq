From Coq Require Import String List Lia Nat Arith.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Program.
From equivChecker Require Import operators utils pset syntax words semantics derivatives expr_deriv opt_algo bounded_checker.
Import ListNotations.

(** * { n : nat | n < N} is Instance of [Equ] and [EquDec] *)

#[global]
Instance nat_fin_equ (N : nat) : Equ ({ n:nat | n < N}).
Proof.
  econstructor. Unshelve. 4: exact (fun x y => proj1_sig x = proj1_sig y).
  - easy.
  - intros x y z H1 H2. now rewrite H1.
  - intros x y H. now rewrite H.
Defined.

#[global]
Instance nat_fin_equ_dec (N : nat) : EquDec ({ n:nat | n < N}).
Proof.
  apply (Build_EquDec _ (nat_fin_equ _)).
  intros x y. simpl. apply Nat.eq_dec.
Defined.

Program Fixpoint seq_wit_aux (N : nat) (i : nat) (Hi : i <= N) : list { n | n < N } :=
  match i with
  | 0 => []
  | S i => i::seq_wit_aux N i _
  end.
Next Obligation.
  apply Le.le_Sn_le_stt, Hi.
Defined.

Program Definition seq_wit (N : nat) : list { n | n < N } :=
  seq_wit_aux N N _.

Theorem helper:
  forall (N : nat) (a : {n : nat | n < N}) i (Ha : proj1_sig a < i) Hi, list_in a (seq_wit_aux N i Hi).
Proof.
  intros N [a Ha1] i Ha2 Hi.
  induction i; try easy; simpl in *.
  assert (Ha : a < i \/ a = i) by lia.
  destruct Ha as [Ha | ->].
  + right. apply IHi, Ha.
  + now left.
Qed.

#[global]
Instance nat_fin (N : nat) : Finite ({ n:nat | n < N}). 
Proof.
  apply (Build_Finite _ _ (seq_wit N)).
  unfold seq_wit. intros.
  apply helper.
  now destruct a as [a Ha].
Defined.

(** * Converting Alphabet nat to Alphabet { n:nat | n < N} *)

Fixpoint max_num_reg_expr (e : regexpr nat) : nat :=
  match e with 
  | Ezero => 0 
  | Eone => 0 
  | Echar i => i
  | Esum e1 e2 => Nat.max (max_num_reg_expr e1) (max_num_reg_expr e2)
  | Ecat e1 e2 => Nat.max (max_num_reg_expr e1) (max_num_reg_expr e2)
  | Estar e => max_num_reg_expr e 
  end.

Fixpoint max_num_omega_reg_expr (e : omega_regexpr nat) : nat :=
  match e with 
  | OEzero => 0
  | OEsum e1 e2 => Nat.max (max_num_omega_reg_expr e1) (max_num_omega_reg_expr e2)
  | OEcat e1 e2 => Nat.max (max_num_reg_expr e1) (max_num_omega_reg_expr e2)
  | OEomega e => max_num_reg_expr e 
  end.

Theorem max_num_reg_correct : 
  forall e, Forall (fun n => n < S (max_num_reg_expr e)) (collect_alphabet_reg e).
Proof.
  induction e; try easy.
  - simpl. constructor; try easy. lia.
  - simpl. apply Forall_app. split.
    + induction IHe1; try easy.
      constructor; try easy. lia.
    + induction IHe2; try easy.
      constructor; try easy. lia.
  - simpl. destruct (non_zero_regexp e1) eqn:H1, (non_zero_regexp e2) eqn:H2; try easy.
    simpl. apply Forall_app. split.
    + induction IHe1; try easy.
      constructor; try easy. lia.
    + induction IHe2; try easy.
      constructor; try easy. lia.
Qed.

Theorem max_num_omega_correct : 
  forall e, Forall (fun n => n < S (max_num_omega_reg_expr e)) (collect_alphabet e).
Proof.
  induction e; try easy.
  - simpl. apply Forall_app. split.
    + induction IHe1; try easy.
      constructor; try easy. lia.
    + induction IHe2; try easy.
      constructor; try easy. lia.
  - simpl. destruct (non_zero_regexp r) eqn:H1, (non_zero_omega_regexp e) eqn:H2; try easy.
    simpl. apply Forall_app. split.
    + pose proof (max_num_reg_correct r). induction H; try easy.
      constructor; try easy. lia.
    + induction IHe; try easy.
      constructor; try easy. lia.
  - simpl. pose proof (max_num_reg_correct r). induction H; try easy.
    constructor; try easy.
Qed.

Definition max_num_expr (e1 : omega_regexpr nat) (e2 : omega_regexpr nat) : nat :=
  Nat.max (max_num_omega_reg_expr e1) (max_num_omega_reg_expr e2).

Inductive Bound (N : nat) : regexpr nat -> Type :=
  | bound_Ezero  : Bound N Ezero
  | bound_Eone   : Bound N Eone
  | bound_Char i (Hi : i < N) : Bound N (Echar i)
  | bound_Esum e1 e2 (H1 : Bound N e1) (H2 : Bound N e2) : Bound N (Esum e1 e2)
  | bound_Ecat e1 e2 (H1 : Bound N e1) (H2 : Bound N e2) : Bound N (Ecat e1 e2)
  | bound_Estar e (He : Bound N e) : Bound N (Estar e).

Lemma bound_le :
  forall e N M, Bound N e -> N <= M -> Bound M e.
Proof.
  intros e N M.
  induction e.
  - intros H1 H2. constructor.
  - constructor.
  - constructor.
    inversion H. lia.
  - intros H1 H2. inversion H1. constructor.
    + now apply IHe1.
    + now apply IHe2.
  - intros H1 H2. inversion H1. constructor.
    + now apply IHe1.
    + now apply IHe2.
  - intros H1 H2. constructor. inversion H1.
    now apply IHe.
Defined.

Theorem compute_bound_correct:
  forall (e : regexpr nat), Bound (S (max_num_reg_expr e)) e.
Proof.
  induction e.
  - constructor.
  - constructor.
  - constructor. simpl. lia.
  - simpl. set (M := max_num_reg_expr e1 ). set (N := max_num_reg_expr e2).
    destruct (Nat.max_dec M N). 
    + rewrite e. constructor. 
      * exact IHe1.
      * apply (bound_le _ (S N)). exact IHe2. rewrite <- e. lia.
    + rewrite e. constructor.
      * apply (bound_le _ (S M)). exact IHe1. rewrite <- e. lia.
      * exact IHe2.
  - simpl. set (M := max_num_reg_expr e1 ). set (N := max_num_reg_expr e2).
    destruct (Nat.max_dec M N). 
    + rewrite e. constructor. 
      * exact IHe1.
      * apply (bound_le _ (S N)). exact IHe2. rewrite <- e. lia.
    + rewrite e. constructor.
      * apply (bound_le _ (S M)). exact IHe1. rewrite <- e. lia.
      * exact IHe2.
  - simpl. now constructor.
Qed.

Fixpoint convert_reg (N : nat) (e : regexpr nat) (H : Bound N e) : regexpr { n : nat | n < N } :=
  match H with
  | bound_Ezero _ => Ezero
  | bound_Eone _ => Eone
  | bound_Char _ i Hi => Echar (exist _ i Hi)
  | bound_Esum _ e1 e2 H1 H2 => Esum (convert_reg N e1 H1) (convert_reg N e2 H2)
  | bound_Ecat _ e1 e2 H1 H2 => Ecat (convert_reg N e1 H1) (convert_reg N e2 H2)
  | bound_Estar _ e He => Estar (convert_reg N e He)
  end.

Inductive Bound_Omega (N : nat) : omega_regexpr nat -> Type :=
  | bound_OEzero : Bound_Omega N OEzero
  | bound_OEsum e1 e2 (H1 : Bound_Omega N e1) (H2 : Bound_Omega N e2) : Bound_Omega N (OEsum e1 e2)
  | bound_OEcat e1 e2 (H1 : Bound N e1) (H2 : Bound_Omega N e2) : Bound_Omega N (OEcat e1 e2)
  | bound_OEomega e (He : Bound N e) : Bound_Omega N (OEomega e).

Lemma bound_omega_le :
  forall e N M, Bound_Omega N e -> N <= M -> Bound_Omega M e.
Proof.
  intros e N M. 
  induction e.
  - constructor.
  - intros H1 H2. inversion H1. constructor.
    + now apply IHe1.
    + now apply IHe2.
  - intros H1 H2. inversion H1. constructor.
     + eapply bound_le; eauto.
    + now apply IHe.
  - intros H1 H2. inversion H1. constructor. 
    eapply bound_le; eauto.
Defined.

Theorem compute_bound_omega_correct:
  forall (e : omega_regexpr nat),
    Bound_Omega (S (max_num_omega_reg_expr e)) e.
Proof.
  induction e; simpl.
  - constructor.
  - remember (max_num_omega_reg_expr e1) as M.
    remember (max_num_omega_reg_expr e2) as N.
    destruct (Nat.max_dec M N) as [Heq | Heq].
    + rewrite Heq. constructor.
      * exact IHe1.
      * eapply bound_omega_le. exact IHe2. lia.
    + rewrite Heq. constructor.
      * eapply bound_omega_le. exact IHe1. lia.
      * exact IHe2.
  - remember (max_num_reg_expr r) as M.
    remember (max_num_omega_reg_expr e) as N.
    destruct (Nat.max_dec M N) as [Heq | Heq].
    + rewrite Heq. constructor. 
      * rewrite HeqM. now apply compute_bound_correct.
      * eapply bound_omega_le. exact IHe. lia.
    + rewrite Heq. constructor.
      * eapply (bound_le _ (S M)).
        rewrite HeqM. now apply compute_bound_correct.
        lia.
      * exact IHe.
  - simpl. constructor.
    apply compute_bound_correct.
Qed.

Fixpoint convert_omega_reg (N : nat) (e : omega_regexpr nat) (H : Bound_Omega N e) : omega_regexpr { n : nat | n < N } :=
  match H with
  | bound_OEzero _ => OEzero
  | bound_OEsum _ e1 e2 H1 H2 => OEsum (convert_omega_reg N e1 H1) (convert_omega_reg N e2 H2)
  | bound_OEcat _ e1 e2 H1 H2 => OEcat (convert_reg N e1 H1) (convert_omega_reg N e2 H2)
  | bound_OEomega _ e He => OEomega (convert_reg N e He)
  end.

(** ** Convert Function *)
Program Definition convert (e1 : omega_regexpr nat ) (e2 : omega_regexpr nat) := 
  let m := S (max_num_expr e1 e2) in 
  let e1' := convert_omega_reg m e1 _ in
  let e2' := convert_omega_reg m e2 _ in 
  (e1', e2').
Next Obligation.
  eapply bound_omega_le.
  apply compute_bound_omega_correct.
  unfold max_num_expr. lia.
Defined.
Next Obligation.
  eapply bound_omega_le.
  apply compute_bound_omega_correct.
  unfold max_num_expr. lia.
Defined.

(** ** Correctness of Converting *)
Fixpoint down_regexp {N : nat} (r : regexpr ({ n : nat | n < N})) : regexpr nat := 
  match r with 
  | Ezero => Ezero 
  | Eone => Eone 
  | Echar i => Echar (proj1_sig i)
  | Esum r1 r2 => Esum (down_regexp r1) (down_regexp r2)
  | Ecat r1 r2 => Ecat (down_regexp r1) (down_regexp r2)
  | Estar r => Estar (down_regexp r)
  end.

Fixpoint down_omega_regexp {N : nat} (e : omega_regexpr ({ n : nat | n < N})) : omega_regexpr nat := 
  match e with 
  | OEzero => OEzero
  | OEsum e1 e2 => OEsum (down_omega_regexp e1) (down_omega_regexp e2)
  | OEcat e1 e2 => OEcat (down_regexp e1) (down_omega_regexp e2)
  | OEomega e => OEomega (down_regexp e)
  end.

Theorem convert_down_regexp_correct :
  forall N r (H: Bound N r), down_regexp (convert_reg N r H) ≃ r.
Proof.
  intros n e H. induction H; try easy.
  - simpl. now rewrite IHBound1, IHBound2.
  - simpl. now rewrite IHBound1, IHBound2.
  - simpl. now rewrite IHBound.
Qed.

Theorem convert_down_omega_regexp_correct :
  forall N e (H: Bound_Omega N e), down_omega_regexp (convert_omega_reg N e H) ≃ e.
Proof.
  intros n e H. induction H; try easy.
  - simpl. now rewrite IHBound_Omega1, IHBound_Omega2.
  - simpl. now rewrite IHBound_Omega, convert_down_regexp_correct.
  - simpl. now rewrite convert_down_regexp_correct.
Qed.

(** ** Equivalence Checker *)

Definition check (e1 : omega_regexpr nat) (e2 : omega_regexpr nat) :=
  let '(e1, e2) := convert e1 e2 in
  bounded_check e1 e2 100.

