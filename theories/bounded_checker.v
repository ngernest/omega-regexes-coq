From Coq Require Import String List Lia Nat.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Program.
From Coq Require Import Arith.Wf_nat.
From equivChecker Require Import utils operators pset syntax words semantics derivatives expr_deriv opt_algo.
Import ListNotations.

(** * Bounded Equivalence Checker *)

Inductive res_opt (A : Type) : Type := 
  | EQUAL : res_opt A
  | NOT_EQUAL : A -> res_opt A 
  | DONT_KNOW : A -> res_opt A.
Arguments EQUAL {_}.
Arguments NOT_EQUAL {_}.
Arguments DONT_KNOW {_}.

Fixpoint find_res {A} (w : coword (algo_option A)) (n : nat) : res_opt A :=
  match w with 
  | FINISHED :? _ => EQUAL
  | CLASH l :? _ => NOT_EQUAL l 
  | CONTINUE l :? w' => match n with 
                        | 0 => DONT_KNOW l 
                        | S n' => find_res w' n'
                        end 
  end.

Definition bounded_check {A} `{DEC: EquDec A} `{@Finite A (@equ_dec_equ _ DEC)} (e1 e2 : omega_regexpr A) (N : nat) :=
  find_res (observe (run_algo [(e1, e2)])) N.

(** ** Soundness *)
Theorem bounded_check_observe_equal {A} `{DEC: EquDec A} `{F: @Finite A (@equ_dec_equ _ DEC)} :
  forall l n, find_res (observe (run_algo l)) n = EQUAL -> exists i, get i (observe (run_algo l)) = FINISHED.
Proof.
  intros l n H.
  induction n in l,H|-*.
  - simpl in *. destruct l.
    + exists 0. simpl. reflexivity.
    + destruct p as [e1 e2]. destruct (trivially_not_equal e1 e2) eqn:T; try easy.
  - simpl in *. destruct l.
    + exists 0. reflexivity.
    + destruct p as [e1 e2]. destruct (trivially_not_equal e1 e2) eqn:T; try easy.
      specialize (IHn _ H). destruct IHn as [i IH].
      now exists (S i). 
Qed.

Theorem bounded_check_correct_equal {A} `{DEC: EquDec A} `{F: @Finite A (@equ_dec_equ _ DEC)} :
  forall e1 e2 n, bounded_check e1 e2 n = EQUAL -> lang_omega_co e1 ≃ lang_omega_co e2.
Proof.
  intros e1 e2 n H.
  pose proof (bounded_check_observe_equal _ _ H) as [i H1].
  apply observe_sound_finished in H1. apply H1; try easy. now left.
Qed.

Theorem bounded_check_observe_not_equal {A} `{DEC: EquDec A} `{F: @Finite A (@equ_dec_equ _ DEC)} :
  forall l l' n, find_res (observe (run_algo l)) n = NOT_EQUAL l' -> exists i, get i (observe (run_algo l)) = CLASH l'.
Proof.
  intros l l' n H.
  induction n in l,l',H|-*.
  - simpl in *. destruct l; try easy.
    destruct p as [e1 e2]. destruct (trivially_not_equal e1 e2) eqn:T; try easy.
    exists 0.
    simpl. rewrite T. now inversion H.
  - simpl in *. destruct l; try easy.
    destruct p as [e1 e2]. destruct (trivially_not_equal e1 e2) eqn:T; try easy.
    + exists 0. simpl. rewrite T. now inversion H.
    + specialize (IHn _ _ H). destruct IHn as [i IH].
      now exists (S i).
Qed.

Theorem bounded_check_correct_not_equal {A} `{DEC: EquDec A} `{F: @Finite A (@equ_dec_equ _ DEC)} :
  forall e1 e2 n l, bounded_check e1 e2 n = NOT_EQUAL l -> ~ (lang_omega_co e1 ≃ lang_omega_co e2).
Proof.
  intros e1 e2 n l H.
  pose proof (bounded_check_observe_not_equal _ _ _ H) as [i H1].
  apply observe_sound_clash in H1.
  intros H2. apply H1. 
  intros e3 e4 H3. destruct H3; try easy.
  now inversion H0 as [-> ->].
Qed.

