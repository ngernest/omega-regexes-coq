From Coq Require Import String List Lia Nat Arith.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Program.
From equivChecker Require Import operators pset.
From equivChecker Require Import syntax words utils.
Import ListNotations.

(** * Semantics of regular expressions *)

(** ** Computational Semantics *)
Fixpoint lang_reg {A : Type} `{Equ A} (e : regexpr A) : @pset (finword A) :=
  match e with
  | Ezero => ∅
  | Eone => {{ [] }}
  | Echar a     => {{ [a] }}
  | Esum r1 r2  => (lang_reg r1) ∪ (lang_reg r2)
  | Ecat r1 r2  => (fun w => exists w1 w2, lang_reg r1 w1 /\ lang_reg r2 w2 /\ w ≃ w1 ++ w2)
  | Estar r     => (fun w => exists l, Forall (lang_reg r) l /\ w ≃ concat l)
  end.

(** ** Declarative Semantics *)
Inductive lang_reg' {A : Type} `{Equ A} : regexpr A -> finword A -> Prop :=
  | lang_reg_one : lang_reg' Eone []
  | lang_reg_char a a' : a ≃ a' -> lang_reg' (Echar a) [a']
  | lang_reg_sum_l r1 r2 w : lang_reg' r1 w -> lang_reg' (r1 + r2) w 
  | lang_reg_sum_r r1 r2 w : lang_reg' r2 w -> lang_reg' (r1 + r2) w 
  | lang_reg_cat r1 r2 w w1 w2 : lang_reg' r1 w1 -> lang_reg' r2 w2 -> w ≃ w1 ++ w2 -> lang_reg' (Ecat r1 r2) (w)
  | lang_reg_star_zero r : lang_reg' (Estar r) []
  | lang_reg_star_cat r w w1 w2 : lang_reg' r w1 -> lang_reg' (Estar r) w2 -> w ≃ w1 ++ w2 -> lang_reg' (Estar r) w.

#[global]
Instance equ_morphism_lang' {A} `{Equ A} : Proper (equ ==> equ ==> iff) (lang_reg).
Proof.
  intros e1 e2 H1.
  induction H1; try easy.
  - intros w1 w2 H2. destruct H2; try easy. 
  - intros w1 w2 H2. destruct H2; try easy.
    split.
    + simpl. intros H3.
      inversion H3; subst. constructor. transitivity x. easy. now transitivity a. 
      now rewrite <- H2.
    + intros H3. inversion H3; subst. constructor. transitivity y; try easy. now transitivity b.
      now rewrite H2.
  - intros w1 w2 H2. split.
    + intros H3. destruct H3.
      * constructor. eapply IHregexpr_equ_ind1; eauto.
      * constructor 2. eapply IHregexpr_equ_ind2; eauto.
    + intros H3. destruct H3.
      * constructor. eapply IHregexpr_equ_ind1; eauto.
      * constructor 2. eapply IHregexpr_equ_ind2; eauto.
  - intros w1 w2 H2. split.
    + intros (w3 & w4 & [H3 [H4 H5]]).
      exists w3, w4. repeat split.
      * now eapply IHregexpr_equ_ind1; eauto. 
      * now eapply IHregexpr_equ_ind2; eauto. 
      * now transitivity w1.
    + intros (w3 & w4 & H3 & H4 & H5). 
      exists w3, w4. repeat split.
      * now eapply IHregexpr_equ_ind1.
      * now eapply IHregexpr_equ_ind2.
      * now transitivity w2.
  - intros w1 w2 H2. split. 
    + intros (l & H3 & H4). 
      exists l. split.
      * clear H4. induction l; try easy. 
        inversion H3; subst. constructor.
        now eapply IHregexpr_equ_ind.
        now apply IHl. 
      * now transitivity w1.
    + intros (l & H3 & H4).
      exists l. split.
      * clear H4. induction l; try easy. 
        inversion H3; subst. constructor.
        now eapply IHregexpr_equ_ind.
        now apply IHl. 
      * now transitivity w2.
Defined.

#[global]
Instance equ_morphism_lang {A} `{Equ A} : Proper (equ ==> equ) (lang_reg).
Proof.
  intros e1 e2 H1. induction H1; try easy.
  - split.
    + intros w H2. unfold In in *. simpl in *. inversion H2; subst. econstructor. 
      now transitivity a. easy.
    + intros w H2. inversion H2; subst. econstructor.
      now transitivity b. easy.
  - split.
    + intros w H2. destruct H2.
      * left. now apply IHregexpr_equ_ind1.
      * right. now apply IHregexpr_equ_ind2.
    + intros w H2. destruct H2.
      * left. now apply IHregexpr_equ_ind1.
      * right. now apply IHregexpr_equ_ind2.
  - split.
    + intros w H2. destruct H2 as (x & y & H2 & H3 & H4). 
      exists x, y. repeat split; try easy. 
      now apply IHregexpr_equ_ind1. now apply IHregexpr_equ_ind2.
    + intros w H2. destruct H2 as (x & y & H2 & H3 & H4). 
      exists x, y. repeat split; try easy. 
      now apply IHregexpr_equ_ind1. now apply IHregexpr_equ_ind2.
  - split.
    + intros w H2. destruct H2 as (l & H2 & H3).
      exists l. split; try easy. 
      clear H3; clear w. induction H2. econstructor.
      constructor. now apply IHregexpr_equ_ind. now apply IHForall.
    + intros w H2. destruct H2 as (l & H2 & H3).
      exists l. split; try easy. 
      clear H3; clear w. induction H2. econstructor.
      constructor. now apply IHregexpr_equ_ind. now apply IHForall. 
Defined.

#[global]
Instance equ_morphism_lang_reg' {A} `{Equ A} : Proper (equ ==> equ ==> iff) (lang_reg').
Proof.
  intros e1 e2 H1.
  induction H1; try easy; intros w1 w2 H2.
  - destruct H2; try easy.
  - destruct H2; try easy. destruct H2; try easy.
    split; intros H2.
    inversion H2; subst. constructor. transitivity a; try easy. now transitivity x.
    inversion H2; subst. constructor. transitivity b; try easy. now transitivity y.
  - split; intros H3.
    + inversion H3; subst.
      apply lang_reg_sum_l. eapply IHregexpr_equ_ind1; eauto.
      apply lang_reg_sum_r. eapply IHregexpr_equ_ind2; eauto.
    + inversion H3; subst.
      apply lang_reg_sum_l. eapply IHregexpr_equ_ind1; eauto.
      apply lang_reg_sum_r. eapply IHregexpr_equ_ind2; eauto.
  - split; intros H3.
    + inversion H3; subst.
      eapply lang_reg_cat.
      eapply IHregexpr_equ_ind1. 2: exact H4.
      reflexivity. 
      eapply IHregexpr_equ_ind2. 2: exact H5.
      reflexivity.
      now transitivity w1.
    + inversion H3; subst.
      eapply lang_reg_cat.
      eapply IHregexpr_equ_ind1. 2: exact H4.
      reflexivity. 
      eapply IHregexpr_equ_ind2. 2: exact H5.
      reflexivity.
      now transitivity w2.
  - split; intros H3.
    + dependent induction H3.
      * destruct w2; try easy.
        apply lang_reg_star_zero.
      * eapply lang_reg_star_cat.
        -- eapply IHregexpr_equ_ind.
           2: exact H3_. reflexivity.
        -- eapply IHlang_reg'2.
           exact H1. exact IHregexpr_equ_ind.
           reflexivity. reflexivity.
        -- now transitivity w.
    + dependent induction H3.
      * destruct w1; try easy.
        apply lang_reg_star_zero.
      * eapply lang_reg_star_cat.
        -- eapply IHregexpr_equ_ind.
           2: exact H3_. reflexivity.
        -- eapply IHlang_reg'2.
           exact H1. exact IHregexpr_equ_ind.
           reflexivity. reflexivity.
        -- now transitivity w.
Defined.

(** ** Equivalence of Computational and Declarative Semantics *)
Theorem equiv_reg_lang {A} `{EQU : Equ A} :
  forall (e : regexpr A),
    lang_reg e ≃ lang_reg' e.
Proof.
  intros e. split.
  - induction e; intros w H; try easy.
    + destruct w; try easy. apply lang_reg_one.
    + inversion H; subst. destruct w1; try easy.
      now apply lang_reg_char.
    + inversion H.
      apply lang_reg_sum_l. now apply IHe1.
      apply lang_reg_sum_r. now apply IHe2.
    + inversion H as (w1 & w2 & H1 & H2 & H3).
      eapply lang_reg_cat; eauto. 
    + unfold subseteq in IHe.
      inversion H as (l & H1 & H2).
      destruct w.
      * apply lang_reg_star_zero.
      * rewrite H2. clear H2.
        induction l; try easy.
        -- now apply lang_reg_star_zero.
        -- simpl. inversion H1; subst.
           eapply lang_reg_star_cat.
           ++ apply IHe. exact H3.
           ++ now apply IHl.
           ++ easy.
  - intros w H. induction H.
    + simpl. constructor.
    + simpl. now constructor.
    + now left.
    + now right.
    + simpl. now exists w1, w2.
    + simpl. now exists [].
    + simpl. inversion IHlang_reg'2 as (l & H2 & H3). 
      exists (w1::l). split.
      * now constructor.
      * simpl. rewrite H1. clear - H3. induction w1; try easy. simpl. now constructor.
Qed.

(** * Inductive semantics of omega regular expressions *)

(** computational slice with one index and one offset *)
Fixpoint slice_aux {A} (w: word A) (i off : nat) : finword A :=
  match off with 
  | 0 => []
  | S off => (w i)::(slice_aux w (S i) off)
  end.

(** Takes an infinite word and returns a *slice*, 
    i.e. finite word with a given length that starts at a given index 
    - `loc` is a pair containing (index, length) *)
Definition slice {A} (w : word A) (loc : nat * nat) : finword A :=
  slice_aux w (fst loc) (snd loc).

Theorem slice_assoc {A} :
  forall (w : word A) i j k, 
  (slice_aux w i j) ++ (slice_aux w (i + j) k) = slice_aux w i (j + k).
Proof.
  intros w i j k. revert w i k.
  induction j.
  - intros w i k. simpl.
    assert ((i+0)%nat = i) as H by lia.
    now rewrite H.
  - intros w i k. simpl. 
    rewrite <- (IHj w (S i) k).
    + assert ((i + S j)%nat = (S i + j)%nat) as H by lia.
      now rewrite H.
Qed.

(** concatenate a language over finite words with a language over infinite words *)
(** [w] is in [L1 • L2] *)
Definition Cat {A} `{Equ A} (L1 : pset (finword A)) (L2 : pset (word A)) (w : word A) : Prop :=
  exists w1 w2,
    L1 w1 /\ L2 w2 /\ w = w1 • w2.

#[global]
Instance Cat_dot {A} `{Equ A} : DotOp2 (pset (finword A)) (pset (word A)) := Cat.

(** takes the number of slice and gives back the index where the slice starts and an offset *)
Definition Chain (f : nat -> (nat * nat)) : Prop :=
  fst (f 0) = 0 /\ 
  (forall n, (snd (f n)) > 0) /\
    forall n, (fst (f n) + snd (f n) = fst (f (S n)))%nat.

(** [w] is in [L^ω] if
    there exists a way to split [w] in [w0 ⋅ w1 ⋅ ... ]
    such that [wi ∈ L1] and [wi ≠ ϵ].
    The split is given by a strictly increasing function [f]
    such all sub word [wi] starts at position [fst f(i)] and has length [snd f(i)] 
    [L] membership of the [wi]s is tested by [slice] 

    - Intuitively, [Omega] ensures that every slice of an infinite word is 
      in the regular language
*)
Definition Omega {A} (L : pset (finword A)) (w : word A) : Prop :=
   exists (f : nat -> (nat * nat)),
      Chain f /\
      forall n, L (slice w (f n)).

(** ** Definition Inductive Semantics of Omega-Regular Expressions *)
Fixpoint omega_lang {A : Type} `{Equ A} (e : omega_regexpr A) : @pset (word A) :=
  match e with
  | OEzero => ∅
  | OEsum e1 e2 => (omega_lang e1 ∪ omega_lang e2)%ops
  | OEcat r e => Cat (lang_reg r) (omega_lang e)
  | OEomega r   => Omega (lang_reg r)
  end.

(** *** Non-computing (aka : relational) version of omega_lang *)
Inductive lang_omega_ind {A : Type} `{Equ A} : omega_regexpr A -> word A -> Prop :=
  | lang_omega_ind_sum_l e1 e2 w :
    lang_omega_ind e1 w -> lang_omega_ind (e1 + e2) w
  | lang_omega_ind_sum_r e1 e2 w :
    lang_omega_ind e2 w -> lang_omega_ind (e1 + e2) w
  | lang_omega_ind_cat r e w1 w2 :
      lang_reg r w1 -> lang_omega_ind e w2 -> lang_omega_ind (r • e) (w1 • w2)
  | lang_omega_ind_omega r w:
      Omega (lang_reg r) w -> lang_omega_ind (OEomega r) w.

(** *** Equivalence of both inductive semantics *)
Theorem equiv_omega_lang {A} `{EQU : Equ A} :
  forall (e : omega_regexpr A),
    lang_omega_ind e ≃ omega_lang e.
Proof.
  intros e. split.
  - intros w H. unfold In in *.
    induction H.
    + now left.
    + now right.
    + simpl. unfold Cat.
      exists w1. exists w2. now split.
    + now simpl.
  - induction e; intros w H; unfold In in *.
    + destruct H.
    + destruct H.
      * apply lang_omega_ind_sum_l. now apply IHe1.
      * apply lang_omega_ind_sum_r. now apply IHe2.
    + destruct H as [w' [H1 [H2 [H3 H4]]]].
      rewrite H4.
      apply lang_omega_ind_cat; try easy.
      now apply IHe.
    + destruct H as [f H].
      apply lang_omega_ind_omega.
      unfold Omega. now exists f.
Qed.

#[global]
Instance equ_morphism_omega_lang {A} `{Equ A} : Proper (equ ==> equ) (omega_lang).
Proof.
  intros e1 e2 H1.
  induction H1.
  - easy.
  - split.
    + intros w H2. inversion H2; subst.
      * econstructor. now apply IHomega_regexpr_equ_ind1.
      * constructor 2. now apply IHomega_regexpr_equ_ind2.
    + intros w H2. inversion H2; subst.
      * econstructor. now apply IHomega_regexpr_equ_ind1.
      * constructor 2. now apply IHomega_regexpr_equ_ind2.
  - split.
    + intros w H2. inversion H2; subst. destruct H3 as (w2 & H3 & H4 & H5).
      econstructor. exists w2. repeat split. apply equ_morphism_lang in H0. apply H0. exact H3.
      now apply IHomega_regexpr_equ_ind. easy.
    + intros w H2. inversion H2; subst. destruct H3 as (w2 & H3 & H4 & H5).
      econstructor. exists w2. repeat split; try easy.
      apply equ_morphism_lang in H0. apply H0. exact H3.
      now apply IHomega_regexpr_equ_ind. easy.
  - split.
    + intros w H2. inversion H2; subst. destruct H1 as (H1 & H3).
      econstructor. split. exact H1. 
      apply equ_morphism_lang in H0. intros n. apply H0. exact (H3 n).
    + intros w H2.  inversion H2; subst. destruct H1 as (H1 & H3).
      econstructor. split. exact H1. 
      apply equ_morphism_lang in H0. intros n. apply H0. exact (H3 n).
Defined.

(** ** Example *)
Section Example.

Definition E1 := Esum (Echar "a"%string) (Echar "b"%string).
Definition E2 := OEomega E1.

Example in_E2 `{Equ string} :
  omega_lang E2 (fun _ => "a"%string).
Proof.
  unfold omega_lang. unfold E2. unfold Omega.
  exists (fun n => (n, 1))%nat. split.
  - unfold Chain. repeat split. (* new *)
    + intros n. simpl. lia.
    + intros n. simpl. lia.
  - intros n. simpl. left.
    constructor. reflexivity. constructor.
Qed.

Example a_in_a_ind `{Equ string} :
  lang_omega_ind (OEomega (Echar "a"%string)) (fun _ => "a"%string).
Proof.
  constructor. unfold Omega.
  exists (fun n => (n, 1))%nat. split.
    - unfold Chain. repeat split. 
      + intros n. simpl. lia.
      + intros n. simpl. lia.
    - intros n. simpl. constructor. 
      reflexivity. 
      constructor.
Qed.

End Example.

(** * CoInductive semantics of omega-regular expressions *)


(** ** Definition Coinductive Semantics *)
(** also sometimes called colang *)

(** [lang_omega_co e w] means w ∈ L_w^co(e) (Definition 3.16 in the thesis) *)
CoInductive lang_omega_co {A} `{Equ A} : omega_regexpr A -> coword A -> Prop :=
  | lang_omega_co_sum_l w e1 e2 :
    lang_omega_co e1 w ->
    lang_omega_co (e1 + e2) w
  | lang_omega_co_sum_r w e1 e2 :
    lang_omega_co e2 w ->
    lang_omega_co (e1 + e2) w
  | lang_omega_co_cat w1 w2 w3 r e :
    lang_reg r w1 ->
    lang_omega_co e w2 ->
    w3 ≃ w1 • w2 ->
    lang_omega_co (r • e) w3
  | lang_omega_co_omega w1 w2 w3 r :
    w1 <> [] ->
    lang_reg r w1 ->
    lang_omega_co (OEomega r) w2 ->
    w3 ≃ w1 • w2 ->
    lang_omega_co (OEomega r) w3.

Theorem lang_omega_co_omega' {A} `{Equ A}:
  forall r w1 w2,
    w1 <> [] ->
    lang_reg r w1 ->
    lang_omega_co (OEomega r) w2 ->
    lang_omega_co (OEomega r) (w1 • w2).
Proof.
  intros.
  econstructor; eauto.
  reflexivity.
Qed.

Theorem colang_cat' {A} `{Equ A}:
  forall r e w1 w2,
    lang_reg r w1 ->
    lang_omega_co e w2 ->
    lang_omega_co (r • e) (w1 • w2).
Proof.
  intros.
  econstructor; eauto.
  reflexivity.
Qed.

(** Language membership (according to the coinductive semantics)
    is preserved up to bisimulation *)
Theorem colang_bisim {A} `{EQU : Equ A} :
  forall e (w1 w2 : coword A),
  lang_omega_co e w1 -> w1 ≃ w2 -> lang_omega_co e w2.
Proof.
  induction e; intros * H1 H2.
  + inversion H1.
  + inversion H1; subst.
    - eapply lang_omega_co_sum_l, IHe1; eauto.
    - eapply lang_omega_co_sum_r, IHe2; eauto.
  + inversion H1; subst.
    econstructor; eauto.
    now rewrite <- H2.
  + generalize w1, w2, H1, H2. clear w1 w2 H1 H2.
    (* Note: here it's important to do induction/co-induction
      and not co-induction/induction.
      Otherwise the guardedness checker is lost !
    *)
    cofix H. intros * H1 H2.
    inversion H1; subst.
    rewrite H2 in H6.
    eapply lang_omega_co_omega; eauto.
Qed.

(** We use the previous lemma to
    prove that lang_omega_co is a morphism with respect to
    regular exression equality, word bissimilarity and propositional equivalence:
    if e1 = e2 and w1 ≃ w2 then lang_omega_co e1 w1 <-> lang_omega_co e2 w2
*)
#[global]
Instance lang_omega_co_morphism {A} `{Equ A}: Proper (eq ==> equ ==> iff) (lang_omega_co).
  intros e1 e2 -> w1 w2 Hbi. split.
  intros. now eapply colang_bisim; eauto.
  intros. now eapply colang_bisim; eauto.
Defined.

#[global]
Instance equ_morphism_colang' {A} `{Equ A} : Proper (equ ==> equ ==> iff) (lang_omega_co).
Proof.
  intros e1 e2 H1. induction H1; try easy.
  - intros w1 w2 H2. split.
    + intros H3. inversion H3; subst.
      * constructor. eapply IHomega_regexpr_equ_ind1; eauto.
      * constructor 2. eapply IHomega_regexpr_equ_ind2; eauto.
    + intros H3. inversion H3; subst.
      * constructor. eapply IHomega_regexpr_equ_ind1; eauto.
      * constructor 2. eapply IHomega_regexpr_equ_ind2; eauto.
  - intros w1 w2 H2. split.
    + intros H3. inversion H3; subst. econstructor. 
      * rewrite <- H0; eauto.
      * eapply IHomega_regexpr_equ_ind. reflexivity. exact H7. 
      * now transitivity w1.
    + intros H3. inversion H3; subst. econstructor.
      * rewrite H0; eauto.
      * eapply IHomega_regexpr_equ_ind. reflexivity. exact H7.
      * now transitivity w2.
  - intros w1 w2 H2. split.
    + assert (forall w3 w4, w3 ≃ w4 -> lang_omega_co (OEomega e1) w3 -> lang_omega_co (OEomega e2) w4).
      { clear w1 w2 H2. cofix IH. 
        intros w3 w4 Hw Hc. inversion Hc; subst. econstructor.
        exact H2. now rewrite <- H0. 
        apply (IH w2 w2). reflexivity. exact H4.
        now transitivity w3.
      }
      now apply H1.
    + assert (forall w3 w4, w3 ≃ w4 -> lang_omega_co (OEomega e2) w3 -> lang_omega_co (OEomega e1) w4).
      { clear w1 w2 H2. cofix IH. 
        intros w3 w4 Hw Hc. inversion Hc; subst. econstructor.
        exact H2. now rewrite H0. 
        apply (IH w2 w2). reflexivity. exact H4.
        now transitivity w3.
      }
      now apply H1.
Qed.

#[global]
Instance equ_morphism_lang_omega_co {A} `{Equ A} : Proper (equ ==> equ) (lang_omega_co).
Proof.
  intros e1 e2 H1. 
  induction H1.
  - easy.
  - split.
    + intros w H2. inversion H2; subst.
      * constructor. now apply IHomega_regexpr_equ_ind1.
      * constructor 2. now apply IHomega_regexpr_equ_ind2.
    + intros w H2. inversion H2; subst.
      * constructor. now apply IHomega_regexpr_equ_ind1.
      * constructor 2. now apply IHomega_regexpr_equ_ind2.
  - split.
    + intros w H2. inversion H2; subst.
      apply IHomega_regexpr_equ_ind in H6. 
      econstructor; eauto. eapply equ_morphism_lang. symmetry. exact H0. easy. 
    + intros w2 H2. inversion H2; subst.
      econstructor; eauto. eapply equ_morphism_lang. exact H0. easy. 
      now apply IHomega_regexpr_equ_ind.
  - split.
    + cofix IH.
      intros w H1. inversion H1; subst.
      econstructor; eauto.
      now rewrite <- H0.
    + cofix IH.
      intros w H1. inversion H1; subst.
      econstructor; eauto.
      now rewrite H0.
Defined.

(** ** Example *)
Section CoExamples.

CoFixpoint aaa :=
  lcons 1 (aaa).

Definition e1 :=
  (Echar 1) • OEomega (Echar 1).

Definition e2 :=
  OEomega (Echar 1).

Theorem a_in_a_co : 
  lang_omega_co e2 (aaa).
Proof.
  cofix H.
  rewrite force_id. simpl.
  apply (lang_omega_co_omega ([1]) aaa); try easy.
  now constructor.
Qed.

Theorem e1_incl_e2 :
  lang_omega_co e1 ⊆ lang_omega_co e2.
Proof.
  intros w H.
  unfold e1, e2.
  inversion H as [ | | w1 w2 ? ? H1 H2 | ]; subst.
  econstructor; eauto.
  simpl in H2. now inversion H2.
Qed.

Theorem e2_incl_e1:
  lang_omega_co e2 ⊆ lang_omega_co e1.
Proof.
  intros w H.
  unfold e1, e2.
  inversion H as [ | | | w1 w2 ? H1 H2 H3 ]; subst.
  econstructor; eauto.
Qed.

Theorem unfold_omega:
  forall {A} `{Equ A} (e : regexpr A) , lang_omega_co (e • (OEomega e)) ≃ lang_omega_co (OEomega e).
Proof.
  intros A e. split.
  - intros w1 H1.
    unfold In in *.
    inversion H1; subst.
    rewrite H5.
    destruct w0.
    + inversion H3; subst.
      assert (w2 ≃ [] • w2) by easy.
      rewrite <- H, H7.
      apply lang_omega_co_omega'; easy.
    + apply lang_omega_co_omega'; try easy.
  - intros w1 H1.
    unfold In in *.
    inversion H1; subst.
    rewrite H4.
    now apply colang_cat'.
Qed.

End CoExamples.

(** * Equivalence of the co-inductive and inductive semantics *)

Lemma length_slice':
  forall {A} (w : word A) i off,
  length (slice w (i, off)) = off.
Proof.
  intros A w i off.
  induction off in i |-*; auto.
  simpl. now erewrite <- IHoff at 2.
Qed.

Lemma length_slice :
  forall {A} (w1: word A) f n, Chain f ->
  length (slice w1 (f n)) = snd (f n).
Proof.
  intros A w1 f n (C1 & C2 & C3).
  destruct (f n) as [i_n off_n]. simpl.
  (* OR apply length_slice'. *)
  induction off_n in i_n |-*; auto.
  simpl. now erewrite <- IHoff_n at 2.
Qed.

(** shifts f one slice *)
Definition chain_shift (f : nat -> nat * nat) : nat -> nat * nat :=
  fun n => (fst (f (S n)) - snd (f 0), snd (f (S n))).

(** gives new word without the first slice *)
Definition word_shift {A} (w : word A) (k : nat) :=
  fun (n : nat) => w (k + n)%nat.

Lemma chain_shift_chain:
  forall f, Chain f -> Chain (chain_shift f).
Proof.
  intros f [C1 [C2 C3]].
  repeat split.
  - unfold chain_shift. simpl.
    rewrite <- (C3 0). lia.
  - unfold chain_shift. now simpl.
  - intros n. unfold chain_shift. simpl.
    rewrite <- (C3 (S n)).
    assert (fst (f (S n)) >= snd (f 0)).
    + rewrite <- C3. induction n.
      * rewrite C1. lia.
      * rewrite <- C3. lia.
    + lia.
Qed.

Lemma word_shift_eq:
  forall {A} (w : word A) woff n,
    n >= woff ->
    word_shift w woff (n - woff) = w n.
Proof.
  intros * Hn.
  destruct n.
  - now destruct woff.
  - unfold word_shift.
    f_equal. lia.
Qed.

Lemma word_shift_eq_slice:
  forall {A} (w : word A) woff n noff,
    n >= woff ->
    slice_aux (word_shift w woff) (n - woff) noff = slice_aux w n noff.
Proof.
  intros * Hn.
  induction noff in n, Hn |-*; auto.
  simpl.
  rewrite <- IHnoff by lia.
  rewrite word_shift_eq by auto.
  now replace (S (n - woff)) with (S n - woff) by lia.
Qed.

Theorem shift_slice:
  forall {A} (n : nat) f (w: word A),
    Chain f ->
    slice w (f (S n)) = slice (word_shift w (snd (f 0))) (chain_shift f n).
Proof.
  intros. unfold slice.
  destruct (f 0) as [i0 off0] eqn:Heq0. simpl.
  erewrite <- word_shift_eq_slice. rewrite Heq0. simpl. eauto.
  destruct H as [C1 [C2 C3]].
  induction n.
  - rewrite <- (C3 0), C1. simpl.
    rewrite Heq0. simpl. lia.
  - rewrite <- (C3 (S n)).
    lia.
Qed.

Inductive option_ {A} (opt : option A) : Type :=
  | is_none : opt = None -> option_ opt
  | is_some x : opt = Some x -> option_ opt.

Theorem option_dec:
  forall {A} (opt : option A), option_ opt.
Proof.
  intros A [].
  - now eright.
  - now left.
Defined.

Definition nth_error_len {B} :
  forall {A} (l : list A) n, n < length l -> nth_error l n = None -> B.
Proof.
  now intros * H1%nth_error_Some H2.
Qed.

Definition nth_safe {A} (l : list A) (i : nat) (H : i < length l) : A :=
  match option_dec (nth_error l i) with
  | is_none _ Hnone => nth_error_len l i H Hnone
  | is_some _ a _ => a
  end.

Theorem nth_error_slice:
  forall {A} (w : word A) i j off,
    i < off ->
    nth_error (slice_aux w j off) i = Some (w (i + j)%nat).
Proof.
  intros.
  induction off in i, j, H |-*; try easy.
  simpl. destruct i; simpl; auto.
  assert (i < off) by lia.
  replace (S (i + j)) with (i + S j)%nat by lia.
  now rewrite IHoff.
Qed.

Theorem nth_safe_slice:
  forall {A} (w : word A) j i off Hlt,
    w (i + j)%nat = nth_safe (slice_aux w j off) i Hlt.
Proof.
  intros.
  assert (Hi : i < off).
  { now rewrite <- (length_slice' w j off). }
  epose proof (H2 := nth_error_slice _ _ _ _ Hi).
  unfold nth_safe.
  destruct option_dec as [H | a H].
  - destruct slice_aux. destruct i; try easy.
    exfalso. apply nth_error_Some in Hlt.
    now apply Hlt.
  - rewrite H2 in H.
    now injection H.
Qed.

Theorem nth_safe_cons:
  forall A a (w : list A) n HSn Hn,
    nth_safe (a::w) (S n) HSn = nth_safe w n Hn.
Proof.
  intros. unfold nth_safe. simpl.
  destruct option_dec; auto.
  exfalso. apply nth_error_Some in Hn.
  now apply Hn.
Qed.

Theorem get_cat_l:
  forall {A} `{Equ A} (w1 : finword A) (w2 : word A) n (Hn : n < length w1),
    (w1 • w2) n = nth_safe w1 n Hn.
Proof.
  induction w1; try easy.
  intros w2 n Hn.
  rewrite (cons_cat a w1 w2 n) at 1.
  destruct n; auto. simpl.
  erewrite IHw1. erewrite nth_safe_cons; eauto.
  Unshelve. simpl in Hn. lia.
Qed.

Theorem get_cat_r:
  forall {A} `{Equ A} (w1 : finword A) (w2 : word A) n,
    n >= length w1 -> (w1 • w2) n = w2 (n - length w1).
Proof.
  induction w1; intros; simpl.
  - now replace (n - 0) with (n) by lia.
  - destruct n; simpl in *; try easy.
    rewrite <- IHw1 by lia.
    now rewrite cons_cat.
Qed.

(** Auxiliary lemma for omega case for semantics inclusion proof *)
Theorem Omega_inv:
  forall {A} `{Equ A} (w1 : word A) e,
    omega_lang (OEomega e) w1 ->
      exists w2 w3, lang_reg e w2 /\ omega_lang (OEomega e) w3 /\ w1 ≃ w2 • w3 /\ w2 <> [].
Proof.
  intros A EQU w1 e H.
  destruct H as (f & Hchain & Hlang).
  exists (slice w1 (f 0)).
  exists (word_shift w1 (snd (f 0))).
  repeat split; auto.
  - simpl. unfold Omega.
    exists (chain_shift f).
    split.
    + now apply chain_shift_chain.
    + intros n. now rewrite <- shift_slice.
  - intros i.
    destruct (f 0) as [i0 off0] eqn:Heq0. simpl.
    pose proof Hchain as [C1 [C2 C3]].
    rewrite Heq0 in C1. simpl in C1; subst.
    destruct (Nat.lt_ge_cases i off0) as [Hlt | Hge].
    + pose proof (length_slice w1 _ 0 Hchain) as H.
      rewrite Heq0 in H. simpl in H.
      rewrite <- H in Hlt.
      rewrite (get_cat_l _ _ _ Hlt).
      unfold slice. simpl.
      rewrite <- nth_safe_slice. 
      f_equal. lia.
    + rewrite get_cat_r by now rewrite length_slice'.
      rewrite length_slice'.
      now rewrite word_shift_eq.
  - destruct Hchain as [C1 [C2 C3]].
    unfold slice.
    rewrite C1.
    pose proof (C2 0) as H.
    destruct (f 0) as [i0 off0]. simpl in *.
    destruct off0; try easy.
Qed.

(** Semantics Inclusion *)
Theorem semantics_inclusion :
  forall A `{Equ A} e (w1 : word A) (w2 : coword A),
    ↑w1 ≃ w2 -> omega_lang e  w1 -> lang_omega_co e w2.
Proof.
  intros A EQU e. 
  induction e.
  - intros w1 w2 H1 H2. destruct H2.
  - intros w1 w2 H1 H2.
    destruct H2.
    + now apply lang_omega_co_sum_l, (IHe1 w1 w2), H.
    + now apply lang_omega_co_sum_r, (IHe2 w1 w2), H.
  - intros w1 w2 H1 H2.
    destruct H2 as (w1_1 & w1_2 & [Hcat1 [Hcat2 Hcat3]]).
    rewrite <- H1. 
    rewrite Hcat3.
    rewrite to_coword_cat.
    apply colang_cat'.
    + easy.
    + now apply (IHe w1_2).
  - cofix H. intros w1 w2 H1 (w3 & w4 & [H2 [H3 [H4 H5 ]]])%Omega_inv.
    apply (lang_omega_co_omega w3 (↑w4)); auto.
    now eapply H.
    now rewrite <- H1, H4, to_coword_cat.
Qed.

