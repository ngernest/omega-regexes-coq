From Coq Require Import String List Lia Nat Arith.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Program.

(** * Type Class for Equivalence Relation *)
Class Equ (A : Type) := {
  equ : A -> A -> Prop;
  equ_refl  :> Reflexive equ;
  equ_trans :> Transitive equ;
  equ_symm  :> Symmetric equ;
}.
Notation "x ≃ y" := (equ x y) (at level 70, no associativity).

(** * Type Class for Decidable Equivalence Relation *)
Class EquDec (A : Type) := {
  equ_dec_equ :> Equ A;
  equ_dec   : forall x y, {equ x y} + {~equ x y};
}.
Notation "x =? y" := (equ_dec x y) (at level 70, no associativity).

(** * Instances for nat and bool *)
#[global]
Instance nat_equ : Equ (nat).
Proof.
  esplit.
  - unfold Reflexive. intros x. apply eq_refl.
  - unfold Transitive. intros x y z H1 H2. now rewrite H1.
  - unfold Symmetric. intros x y H. now rewrite H.
Defined.

#[global]
Instance nat_equ_dec : EquDec (nat).
Proof.
  econstructor.
  intros. apply Nat.eq_dec.
Defined.

#[global]
Instance bool_equ : Equ (bool).
Proof.
  esplit.
  - unfold Reflexive. intros x; destruct x; easy.
  - unfold Transitive. intros x y z H1 H2. now rewrite H1.
  - unfold Symmetric. intros x y H. now rewrite H.
Defined.

