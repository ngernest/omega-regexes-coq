From Coq Require Import String List Lia.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Program.
From equivChecker Require Import utils operators pset syntax words semantics.
Import ListNotations.

(** * Derivatives of Languages *)

(** [deriv_a] is the derivative of a language [L] over infintie words 
     with respect to symbol [a] *)
Definition deriv_a {A : Type} (a : A) (L : pset (coword A)) : pset (coword A) :=
  (fun w => L (lcons a w)).

(** [deriv_a] is the derivative of a language [L] over finite words 
     with respect to symbol [a] *)
Definition regular_deriv_a {A : Type} (a : A) (L : pset (finword A)) : pset (finword A) :=
  (fun w => L (cons a w)).

(** [deriv_w] is the word derivative of a language [L] over infinite words 
    with respect to the finite word [w] *)
Definition deriv_w {A: Type} (w : finword A) (L : pset (coword A)) : pset (coword A) := 
  (fun w' => L (w • w')).

Notation "'Δ(' a , L ')'" := (deriv_a a L) (at level 80).
Notation "'δ(' a , L ')'" := (regular_deriv_a a L) (at level 80).

Theorem deriv_eq {A : Type} :
  forall (L1 L2 : pset (coword A)), 
    L1 ≃ L2 <-> forall a, Δ(a, L1) ≃ Δ(a, L2).
Proof.
  intros. split.
  + intros [H1 H2].
    split.
    - intros w Hw. unfold In, deriv_a in *.
      unfold subseteq in *; unfold In in *.
      now apply H1.
    - intros w Hw. unfold In, deriv_a in *.
      unfold subseteq in *; unfold In in *.
      now apply H2.
  + intros H.
    split.
    - unfold deriv_a, subseteq, In in *. 
      intros x H1.
      destruct x as [x0 xr].
      specialize (H x0).
      now apply H.
    - unfold deriv_a, subseteq, In in *.
      intros x H2.
      destruct x as [x0 xr].
      specialize (H x0).
      now apply H.
Qed.

(** make deriv_eq an instance of Proper ((eq ==> equ ==> equ) *)
#[global]
Instance deriv_a_morphism {A} : Proper (eq ==> equ ==> equ) (@deriv_a A).
Proof.
  intros a b H1 L1 L2 H2. 
  split.
  - intros w H. unfold In in *. 
    unfold deriv_a in *.
    destruct H1; unfold subseteq in *; unfold In in *.
    now apply H2.
  - intros w H. unfold In in *.
    unfold deriv_a in *.
    destruct H1.
    now apply H2.
Defined.

(** * Declarative Equivalence Checker *)

Inductive rtclosure {A} (R : A -> A -> Prop) : A -> A -> Prop :=
  | rt_refl x : rtclosure R x x
  | rt_step x y z :
    rtclosure R x y -> R y z -> rtclosure R x z.

#[global]
Instance rtclosureRefl {A} (R : A -> A -> Prop) : Reflexive (rtclosure R).
Proof.
  intros x.
  apply rt_refl.
Qed.

#[global]
Instance rtclosureTrans {A} (R : A -> A -> Prop) : Transitive (rtclosure R).
Proof.
  intros x y z H1 H2.
  induction H2 in x, H1 |-*.
  - easy.
  - apply (rt_step _ _ y).
    + now apply IHrtclosure.
    + exact H.
Qed.

Reserved Notation "E1 '->Δ' E2" (at level 80).
Reserved Notation "E1 '->*Δ' E2" (at level 80).

(** An equation is a set of omega-regular expression pairs *)
Definition Equations A := @pset (omega_regexpr A * omega_regexpr A).

#[global]
Instance omega_regexpr_equ_pair {A} `{Equ A} : Equ (omega_regexpr A * omega_regexpr A).
Proof.
  esplit. Unshelve. 4: exact (fun '(e1, e2) '(e3, e4) => equ e1 e3 /\ equ e2 e4).
  - now intros [e1 e2]. 
  - now intros [e1 e2] [e3 e4] [e5 e6] [-> ->] [-> ->].
  - now intros [e1 e2] [e3 e4] [-> ->].
Defined.

#[global]
Instance omega_regexpr_equ_dec_pair {A} `{EquDec A} : EquDec (omega_regexpr A * omega_regexpr A).
Proof.
  apply (Build_EquDec _ omega_regexpr_equ_pair).
  intros [e1 e2] [e3 e4]. 
  destruct (equ_dec e1 e3), (equ_dec e2 e4).
  + now left.
  + right. simpl. intros [H1 H2]. now apply n.
  + right. simpl. intros [H1 H2]. now apply n.
  + right. simpl. intros [H1 H2]. now apply n.
Defined.

(** ** Step of the Algorithm *)

(** [step] represents one step in the declarative algorithm for checking
    omega-regular expression equivalence *)
Inductive step {A} `{Equ A} : Equations A -> Equations A -> Prop :=
  | deriv E e1 e2 e1' e2' :
    (forall a, lang_omega_co (e1' a) ≃ deriv_a a (lang_omega_co e1)) ->
    (forall a, lang_omega_co (e2' a) ≃ deriv_a a (lang_omega_co e2)) ->
    E ∪ {{(e1, e2)}} ->Δ E ∪ bigUnion (fun a => {{(e1' a, e2' a)}})
  | delete E e1 e2 :
    lang_omega_co e1 ≃ lang_omega_co e2 ->
    E ∪ {{(e1, e2)}} ->Δ E
where "E1 ->Δ E2" := (step E1 E2).

Definition steps {A} `{Equ A} := rtclosure (@step A _).
Notation "E1 ->*Δ E2" := (steps E1 E2).

Definition Valid {A} `{Equ A} (E : Equations A) :=
  forall e1 e2, E (e1, e2) -> lang_omega_co e1 ≃ lang_omega_co e2.

Definition equiv {A} `{Equ A} (E E' : Equations A) :=
  Valid E <-> Valid E'.

#[global]
Instance equivEquiv {A} (EQU: `{Equ A}) : Equivalence (@equiv A _ ).
Proof.
  split.
  - intros e. split; easy.
  - intros e1 e2 [H1 H2].
    split; easy.
  - intros e1 e2 e3 [H1 H2] [H3 H4].
    split.
    + intros H. now apply H3, H1.
    + intros H. now apply H2, H4.
Qed.

(** ** Soundness *)
Theorem step_sound :
  forall A (Dec : Equ A) (E E' : Equations A), E ->Δ E' -> equiv E E'.
Proof.
  intros A Dec E E' H.
  split.
  - destruct H as [E e1 e2 e1' e2' H1 H2|E e1 e2 H0].
    + intros H. unfold Valid in *.
      intros e3 e4 H'.
      destruct H' as [H'|H'].
      * apply H. now left.
      * unfold In, bigUnion in H'. destruct H' as [a [-> ->]].
        rewrite H1, H2.
        rewrite H. reflexivity. now right.
    + intros H. unfold Valid in *.
      intros e3 e4 H1.
      apply H. now left.
  - destruct H as [E e1 e2 e1' e2' H1 H2|E e1 e2 H0].
    + intros H. unfold Valid in *.
      intros e3 e4 H'.
      destruct H' as [H'|H'].
      * apply H. now left.
      * unfold In in H'.
        destruct H' as [-> ->].
        apply deriv_eq.
        intros a.
        pose proof (H (e1' a) (e2' a)) as Sol.
        assert ((E ∪ bigUnion (fun a => {{(e1' a, e2' a)}})) (e1' a, e2' a)).
        { right. unfold In, bigUnion. now exists a. }
        rewrite <- H1, <- H2. apply (Sol H0).
    + intros H. unfold Valid in *.
      intros e3 e4 H'.
      destruct H'.
      * now apply H.
      * unfold In in H1.
        now destruct H1 as [-> ->].
Qed.

Theorem steps_sound {A} (EQU: `{Equ A}):
  forall (E E' : Equations A), E ->*Δ E' -> equiv E E'.
Proof.
  intros E E' H.
  split.
  - intros H1. unfold Valid in *.
    induction H.
    + apply H1.
    + pose proof (step_sound _ _ _ _ H0) as H3. unfold equiv, Valid in H3. destruct H3 as [H3 H4].
      apply H3. now apply IHrtclosure.
  - intros H1. unfold Valid in *.
    induction H.
    + apply H1.
    + pose proof (step_sound _ _ _ _ H0) as H3. unfold equiv, Valid in H3. destruct H3 as [H3 H4].
      apply IHrtclosure. now apply H4.
Qed.

Theorem equivalence_checking :
  forall {A} `{Equ A} (e1 e2 : omega_regexpr A),
    {{(e1, e2)}} ->*Δ ∅ -> lang_omega_co e1 ≃ lang_omega_co e2.
Proof.
  intros A EQU e1 e2 H.
  apply steps_sound in H as [H1 H2].
  now apply H2.
Qed.

