From Coq Require Import Classes.RelationClasses.
From Coq Require Import Classes.Morphisms.
From equivChecker Require Import operators utils.

(** * Operations over Sets *)

Section Pset.

Variable A : Type.

Definition pset := (A -> Prop).

Definition inter (P Q : pset) : pset :=
  fun x => P x /\ Q x.

Definition union (P Q : pset) : pset :=
  fun x => P x \/ Q x.

Definition bigUnion {B : Type} (P : B -> pset) : pset :=
  fun x => exists (i : B), (P i) x.

Definition bigInter {B : Type} (P : B -> pset) : pset :=
  fun x => forall (i : B), (P i) x.

Definition diff (P Q : pset) : pset :=
  fun x => P x /\ ~Q x.

Definition comp (P : pset) : pset :=
  fun x => ~P x.

Definition subseteq (P Q : pset) :=
  forall x, P x -> Q x.

Definition equiv (P Q : pset) :=
  subseteq P Q /\ subseteq Q P.

#[global]
Instance pset_equ : Equ pset.
Proof.
  eapply (Build_Equ _ equiv); firstorder.
Defined.

Definition subset (P Q : pset) :=
  subseteq P Q /\ exists x, Q x /\ ~Q x.

End Pset.

(** * Notation for Sets *)
#[global]
Instance union_cup (A : Type) : CupOp (pset A) := union A.
#[global]
Instance inter_cap (A : Type) : CapOp (pset A) := inter A.

#[global]
Instance subseteq_subseteq (A : Type) : SubseteqOp (pset A) := subseteq A.
#[global]
Instance subset_subset (A : Type) : SubsetOp (pset A) := subset A.

Notation "{{ x }}" := (fun t => t ≃ x).
Notation "{{ x ; y ; .. ; z }}" := (fun t => ( .. (t ≃ x \/ t ≃ y) .. \/ t ≃ z)).
Notation "∅" := (fun _ => False).

Arguments bigUnion {_} {_}.
Arguments bigInter {_} {_}.

(** * Theorems about Union *)
Lemma union_comm {A}:
  forall (a b : pset A), a ∪ b ≃ b ∪ a.
Proof.
  intros a b; firstorder.
Qed.

Lemma union_assoc {A} : 
  forall (a b c : pset A), (a ∪ b) ∪ c ≃ a ∪ (b ∪ c).
Proof.
  intros a b c; firstorder.
Qed.

Lemma union_neutral {A} :
  forall (a : pset A), ∅ ∪ a ≃ a.
Proof.
  intros p; firstorder.
Qed.

#[global]
Instance union_morphism {A} : Proper (equ ==> equ ==> equ) (union A).
Proof.
  intros p q H1 r s H2; firstorder.
Qed.

#[global]
Instance inter_morphism {A} : Proper (equ ==> equ ==> equ) (inter A).
Proof.
  intros p q H1 r s H2; firstorder.
Qed.

