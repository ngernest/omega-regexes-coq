From equivChecker Require Import utils operators.
From Coq Require Import List.
From Coq Require Import Classes.Morphisms.
Import ListNotations.

(** * Finite Words *)

Definition finword (A : Type) := list A.

Inductive finword_pointwise_eq {A} `{Equ A} : finword A -> finword A -> Prop :=
  | empty : finword_pointwise_eq [] []
  | full x w1 y w2 : equ x y -> finword_pointwise_eq w1 w2 -> 
      finword_pointwise_eq (x::w1) (y::w2).

#[global]
Instance finword_equ {A} `{Equ A} : Equ (finword A).
Proof.
  eapply (Build_Equ _ finword_pointwise_eq).
  - intros x. induction x; constructor; try easy. 
  - intros x y z H1. induction H1 in z|-*; intros H2; try easy.
    inversion H2; subst. apply IHfinword_pointwise_eq in H7.
    econstructor; try easy. etransitivity; eauto.
  - intros x y H1. induction H1.
    + econstructor.
    + now econstructor. 
Defined.

#[global]
Instance finword_equ_dec {A} `{EquDec A} : EquDec (finword A).
Proof.
  esplit.
  intros x y. induction x in y |-*.
  + destruct y. repeat econstructor.
    now right. 
  + destruct y. now right.
    destruct (IHx (y)), (equ_dec a a0).
    * left. now constructor.
    * right. now inversion 1.
    * right. now inversion 1.
    * right. now inversion 1.
Defined.

#[global]
Instance finword_pointwise_eq_refl {A} `{Equ A} : Reflexive finword_pointwise_eq.
Proof.
  intros x. induction x; constructor; try easy.
Defined.

#[global]
Instance finword_pointwise_eq_trans {A} `{Equ A} : Transitive finword_pointwise_eq.
Proof.
  intros x y z H1. induction H1 in z|-*; intros H2; try easy.
  inversion H2; subst. apply IHfinword_pointwise_eq in H7.
  econstructor; try easy. etransitivity; eauto.
Defined.

#[global]
Instance finword_pointwise_eq_symm {A} `{Equ A} : Symmetric finword_pointwise_eq.
Proof.
  intros x y H1. induction H1.
  + econstructor.
  + now econstructor. 
Defined.

(** * Infinite Words as Functions *)

(** words over A as functions from nat to A *)
Definition word (A : Type) := nat -> A.

(** equality of words (this definition avoids to rely on functional extensionality) *)
Definition word_ext {A} (w1 w2 : word A) : Prop :=
  forall i, w1 i = w2 i.

#[global]
Instance word_equ {A} `{Equ A} : Equ (word A).
Proof.
  eapply (Build_Equ _ word_ext).
  - firstorder.
  - intros x y z H1 H2 i.
    now rewrite <- H2, <- H1.
  - intros x y Heq i.
    now rewrite Heq.
Defined.

(** Concatenating a letter at the begining of a word *)
Definition fcons {A} (x : A) (w : word A) : word A :=
  fun n => match n with 0 => x | S n => w n end.

(** Droping the first letter of a word *)
Definition ftail {A} (w : word A) : word A :=
  fun n => w (S n).

(** ftail respects words equalities.
    In order to let Coq know this fact, we use 
    typeclasses. Intuitively, a typeclass
    is a way to equip a type or a function with
    some custom properties.    
    Here the "Proper (equ ==> equ) ftail" class means
    tha ftail is a function such that if "x ≃ y" then "ftail x ≃ ftail y".
    By proving this as an instance of the "Proper" typeclass,
    Coq is now automatically knows this fact and can use it
    automatically when trying to rewrite a ≃ hypothesis in a goal
    of the form ftail _ ≃ ftail _.
*)
#[global]
Instance ftail_morphism {A} `{Equ A} : Proper (equ ==> equ) (@ftail A).
Proof.
  intros w1 w2 Heq i.
  apply (Heq (S i)).
Defined.

(** fcons also respects equalities !
    If a = b and wa ≃ wb then fcons a wa ≃ fcons b wb
*)
#[global]
Instance fcons_morphism {A} `{Equ A} : Proper (eq ==> equ ==> equ) (@fcons A).
Proof.
  intros x y H1 w1 w2 H2 i.
  destruct i.
  - now rewrite H1.
  - simpl. apply (H2 i).
Defined.

(** ftail is a left inverse for fcons *)
Lemma ftail_fcons {A} `{Equ A} :
  forall (x : A) (w : word A),
    ftail (fcons x w) ≃ w.
Proof.
  now intros.
Qed.

(** concatenate a finite with an infinite word *)
Fixpoint cat {A} (w1: finword A) (w2: word A) :=
  match w1 with 
  | nil => w2 
  | a::w => fcons a (cat w w2)
  end.

#[global]
Instance cat_dot A : DotOp2 (finword A) (word A) := cat.

(** * Words as Coinductive Lists *)

CoInductive coword (A : Type) :=
  | lcons (x : A) (xs : coword A).
Arguments lcons {_}.
Infix ":?" := lcons (at level 80).

Definition force {A} (w : coword A) :=
  match w with
  | lcons x w => lcons x w
  end.

Theorem force_id:
  forall A (w : coword A), w = force w.
Proof.
  now intros A [].
Qed.

(** tail of a coword (remove first element) *)
Definition ltail {A} (w : coword A) :=
  match w with
  | _ :? w => w
  end.

(** Definition bisimular of two cowords: tail the same and first symbol *)
CoInductive bisim {A} : coword A -> coword A -> Prop :=
  | bisim_intro (x : A) xs ys:
    bisim xs ys ->
    bisim (lcons x xs) (lcons x ys).

(**
  bisim is reflexive.
  Declaring this fact as an instance of the class [Reflexive]
  allows to use the tactic "reflexivity" to preove "x ≃ x".
*)
#[global]
Instance bisim_refl {A} `{Equ A} : Reflexive (@bisim A).
Proof.
  cofix Hrefl.
  intros [].
  apply bisim_intro.
  now apply Hrefl.
Qed.

(** bisim is transitive *)
#[global]
Instance bisim_trans {A} `{Equ A} : Transitive (@bisim A).
Proof.
  cofix Htrans.
  intros a b c H1 H2.
  inversion H1; subst. 
  inversion H2; subst.
  constructor.
  eapply Htrans; eauto.
Qed.

(**
    bisim is symmetric.
    Declaring this fact as an intance of the class [Symmetric]
    allows to use the tactic "symmetry" to prove "x ≃ y" from "y ≃ x".
*)
#[global]
Instance bisim_symm {A} `{Equ A} : Symmetric (@bisim A).
Proof.
  cofix Hsymm.
  intros a b [? xs ys Hbi].
  constructor.
  now apply Hsymm.
Qed.

#[global]
Instance bisim_equ {A} `{Equ A} : Equ (coword A).
Proof.
  eapply (Build_Equ _ bisim); intuition.
Defined.

#[global]
Instance lcons_bisim {A} `{Equ A} : Proper (eq ==> equ ==> equ) (@lcons A).
  intros x y -> w1 w2 Hbi.
  now constructor.
Defined.

(** Concatenation of a finite word and a infinite (co)word *)
Fixpoint cocat {A} (w1 : finword A) (w2 : coword A) :=
  match w1 with
  | [] => w2
  | x::xs => lcons x (cocat xs w2)
  end.

#[global]
Instance cocat_dot {A} : DotOp2 (finword A) (coword A) := cocat.

#[global]
Instance cocat_morphism {A} `{Equ A} : Proper (eq ==> equ ==> equ) (@cocat A).
  intros w1 ? <- w2 w3 Hbi.
  induction w1.
  - easy.
  - simpl. now constructor. 
Defined.

Theorem cat_bisim_1:
  forall {A} `{Equ A} (w1 : finword A) (w2 w3 : coword A),
    w1 • w2 ≃ w3 ->
      exists w3', w3 = w1 • w3' /\ w2 ≃ w3'.
Proof.
  intros A EQU w1 w2 w3 H.
  induction w1 in w2, w3, H |-*.
  + now exists w3.
  + simpl in *. destruct w3.
    inversion H; subst.
    apply IHw1 in H1 as [w3' [-> Hw3']]. 
    now exists w3'.
Qed.

Theorem cat_bisim_2:
  forall {A} `{Equ A} (w1 : finword A) (w2 w3 : coword A),
    w2 ≃ w3 -> w1 • w2 ≃ w1 • w3.
Proof.
  now intros A EQU w1 w2 w3 ->.
Qed.

Theorem equal_to_bisim {A : Type} `{Equ A} : 
  forall (x y : coword A), x = y -> x ≃ y.
Proof.
  intros x y H1. 
  rewrite H1. reflexivity.
Qed.

(** * Equivalence of Words and Cowords *)

(* Function to translate a word (inductive) to a (co)word (coinductive) *)
CoFixpoint to_coword {A} (w : word A) :=
  lcons (w 0) (to_coword (ftail w)).
Notation "↑" := to_coword.

(** to_word is a morphism wrt to word equality and coword bissimilarity.
    If w1 ≃ w2 then to_coword w1 ≃ to_coword w2.
*)
#[global]
Instance to_coword_morphism {A} `{EQU : Equ A} : Proper (equ ==> equ) (@to_coword A).
Proof.
  cofix H.
  intros w1 w2 Heq.
  rewrite (force_id _ (↑w1)).
  rewrite (force_id _ (↑w2)).
  simpl. rewrite Heq.
  constructor.
  apply H, ftail_morphism, Heq.
Defined.

Theorem to_coword_fcons:
  forall {A} `{Equ A} (a : A) w,
    ↑(fcons a w) ≃ lcons a (↑w).
Proof.
  intros.
  rewrite (force_id _ (↑(fcons _ _))). simpl.
  constructor. now rewrite ftail_fcons.
Qed.

Theorem to_coword_cat:
  forall {A} `{Equ A} (w1 : finword A) (w2 : word A), ↑(w1 • w2) ≃ w1 • ↑w2.
Proof.
  induction w1; cbn.
  - easy.
  - intros w2.
    rewrite to_coword_fcons. 
    constructor. apply IHw1.
Defined.

Lemma cons_cat:
  forall {A} `{Equ A} (a : A) (w1 : finword A) (w2 : word A),
    (a :: w1) • w2 ≃ fcons a (w1 • w2).
Proof.
  easy.
Qed.

Lemma fcons_S_n:
  forall {A} (a : A) (w : word A) n,
    (fcons a w) (S n) = w n.
Proof.
  reflexivity.
Qed.

