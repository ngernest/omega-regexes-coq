From Coq Require Import String List Lia Nat Arith.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Program.
From equivChecker Require Import operators pset utils.
Import ListNotations.

(** * Syntax of Regular Expressions *)

(** Regular expressions over an alphabet [A] *)
Inductive regexpr (A : Type) : Type :=
  | Ezero
  | Eone
  | Echar (a : A)
  | Esum (r1 : regexpr A) (r2 : regexpr A)
  | Ecat (r1 : regexpr A) (r2 : regexpr A)
  | Estar (r : regexpr A).
Arguments Ezero {_}.
Arguments Eone {_}.
Arguments Echar {_}.
Arguments Esum {_}.
Arguments Ecat {_}.
Arguments Estar {_}.

#[global]
Instance Ecat_dot A : DotOp1 (regexpr A) := Ecat.

#[global]
Instance Esum_add A : AddOp (regexpr A) := Esum.

(** * Syntax of Omega-Regular Expressions *)

(** Omega-regular expressions over an alphabet [A] *)
Inductive omega_regexpr (A : Type) : Type :=
  | OEzero 
  | OEsum (e1 : omega_regexpr A) (e2 : omega_regexpr A)
  | OEcat (r : regexpr A) (e : omega_regexpr A)
  | OEomega (r : regexpr A).
Arguments OEzero {_}.
Arguments OEsum {_}.
Arguments OEcat {_}.
Arguments OEomega {_}.

#[global]
Instance OEcat_dot A : DotOp2 (regexpr A) (omega_regexpr A) := OEcat.

#[global]
Instance OEsum_add A : AddOp (omega_regexpr A) := OEsum.

(** * Decidable Equivalence Relation for Regular Expressions *)

Inductive regexpr_equ_ind {A} `{Equ A} : regexpr A -> regexpr A -> Prop := 
  | REIzero : regexpr_equ_ind Ezero Ezero
  | REIone : regexpr_equ_ind Eone Eone 
  | REIchar a b : equ a b -> regexpr_equ_ind (Echar a) (Echar b)
  | REIsum e1 e2 e3 e4 : regexpr_equ_ind e1 e3 -> regexpr_equ_ind e2 e4 -> regexpr_equ_ind (Esum e1 e2) (Esum e3 e4)
  | REIcat e1 e2 e3 e4 : regexpr_equ_ind e1 e3 -> regexpr_equ_ind e2 e4 -> regexpr_equ_ind (Ecat e1 e2) (Ecat e3 e4)
  | REIstar e1 e2 : regexpr_equ_ind e1 e2 -> regexpr_equ_ind (Estar e1) (Estar e2).

#[global]
Instance regexpr_equ_ind_refl {A} `{Equ A} : Reflexive (regexpr_equ_ind).
Proof.
  intros x. induction x; try econstructor; easy.
Defined.

#[global]
Instance regexpr_equ_ind_trans {A} `{Equ A} : Transitive (regexpr_equ_ind).
Proof.
  intros x y z H1. induction H1 in z|-*; try easy.
  - inversion 1; subst. constructor. now (transitivity b).
  - inversion 1; subst. constructor. 
    + now eapply (IHregexpr_equ_ind1).
    + now eapply (IHregexpr_equ_ind2).
  - inversion 1; subst. constructor.
    + now eapply IHregexpr_equ_ind1.
    + now eapply IHregexpr_equ_ind2.
  - inversion 1; subst. constructor.
    now eapply IHregexpr_equ_ind.
Defined.

#[global]
Instance regexpr_equ_ind_sym {A} `{Equ A} : Symmetric (regexpr_equ_ind).
Proof.
  intros x y H1. induction H1; try easy; now constructor.
Defined.

#[global]
Instance regexpr_equ {A} `{Equ A} : Equ (regexpr A).
Proof.
  esplit. Unshelve. 4: exact regexpr_equ_ind. 
  - exact regexpr_equ_ind_refl.
  - exact regexpr_equ_ind_trans.
  - exact regexpr_equ_ind_sym.
Defined.

#[global]
Instance regexpr_equ_dec {A} `{EquDec A} : EquDec (regexpr A).
Proof.
  eapply (Build_EquDec _ regexpr_equ).
  intros x y. induction x in y|-*; destruct y; try now right.
  + now left.
  + now left.
  + destruct (equ_dec a a0).
    left. now constructor. right. now inversion 1.
  + destruct (IHx1 y1), (IHx2 y2).
    * left. now constructor.
    * right. now inversion 1.
    * right. now inversion 1.
    * right. now inversion 1.
  + destruct (IHx1 y1), (IHx2 y2).
    * left. now constructor.
    * right. now inversion 1.
    * right. now inversion 1.
    * right. now inversion 1.
  + destruct (IHx y).
    left. now constructor.
    right. now inversion 1.
Defined.

(** * Decidable Equivalence Relation for Omega-Regular Expressions *)

Inductive omega_regexpr_equ_ind {A} `{Equ A} : omega_regexpr A -> omega_regexpr A -> Prop :=
  | OREIzero : omega_regexpr_equ_ind (OEzero) (OEzero)
  | OREIsum e1 e2 e3 e4 :
    omega_regexpr_equ_ind e1 e2 ->
    omega_regexpr_equ_ind e3 e4 ->
    omega_regexpr_equ_ind (e1 + e3) (e2 + e4)
  | OREIcat e1 e2 e3 e4 :
    e1 ≃ e2 ->
    omega_regexpr_equ_ind e3 e4 ->
    omega_regexpr_equ_ind (e1 • e3) (e2 • e4)
  | OREIomega e1 e2 :
    e1 ≃ e2 -> omega_regexpr_equ_ind (OEomega e1) (OEomega e2).

#[global]
Instance omega_regexpr_equ_ind_refl {A} `{Equ A} : Reflexive (omega_regexpr_equ_ind).
Proof.
  intros x.
  induction x; now constructor.
Defined.

#[global]
Instance omega_regexpr_equ_ind_trans {A} `{Equ A} : Transitive (omega_regexpr_equ_ind).
Proof.
  intros x y z H1. induction H1 in z|-*; destruct z; try easy.
  - intros H2. constructor; inversion H2; subst.
    + now apply IHomega_regexpr_equ_ind1.
    + now apply IHomega_regexpr_equ_ind2.
  - inversion 1; subst. constructor.
    + now transitivity e2.
    + now apply IHomega_regexpr_equ_ind.
  - inversion 1; subst. constructor. now transitivity e2.
Defined.

#[global]
Instance omega_regexpr_equ_ind_sym {A} `{Equ A} : Symmetric (omega_regexpr_equ_ind).
Proof.
 intros x y H1. induction H1; now constructor. 
Defined.

#[global]
Instance omega_regexpr_equ {A} `{EQU : Equ A} : Equ (@omega_regexpr A).
Proof.
  esplit. Unshelve. 4: exact omega_regexpr_equ_ind.
  - exact omega_regexpr_equ_ind_refl.
  - exact omega_regexpr_equ_ind_trans.
  - exact omega_regexpr_equ_ind_sym.
Defined.

#[global]
Instance omega_regexpr_equ_dec {A} `{EQU : EquDec A} : EquDec (@omega_regexpr A).
Proof.
  eapply (Build_EquDec _ omega_regexpr_equ).
  intros x y. 
  induction x in y|-*; destruct y; try now right.
  + now left.
  + destruct (IHx1 y1), (IHx2 y2).
    * left. now constructor.
    * right. now inversion 1.
    * right. now inversion 1.
    * right. now inversion 1.
  + destruct (IHx y), (equ_dec r r0).
    * left. now constructor.
    * right. now inversion 1.
    * right. now inversion 1.
    * right. now inversion 1.
  + destruct (equ_dec r r0).
    * left. now constructor.
    * right. now inversion 1.
Defined.

(** * Boolean Decider for Regular and Omega-Regular Expressions *)

Fixpoint syntactic_equal_regexpr {A} `{EquDec A} (r1 r2 : regexpr A) : bool :=
  match r1, r2 with
  | Ezero, Ezero => true 
  | Eone, Eone => true
  | Echar a, Echar b => if a =? b then true else false
  | Esum s t, Esum s' t' => 
      syntactic_equal_regexpr s s' && syntactic_equal_regexpr t t'
  | Ecat s t, Ecat s' t' => 
      syntactic_equal_regexpr s s' && syntactic_equal_regexpr t t'
  | Estar r, Estar r' => syntactic_equal_regexpr r r'
  | _ , _ => false
  end.

Fixpoint syntactic_equal_omegaregexpr {A} `{EquDec A} (e1 e2 : omega_regexpr A) : bool :=
  match e1, e2 with 
  | OEzero, OEzero => true
  | OEsum f g, OEsum f' g' => 
      syntactic_equal_omegaregexpr f f' && syntactic_equal_omegaregexpr g g'
  | OEcat f g, OEcat f' g' => 
      syntactic_equal_regexpr f f' && syntactic_equal_omegaregexpr g g'
  | OEomega e, OEomega e' => syntactic_equal_regexpr e e'
  | _ , _ => false
  end.

