From Coq Require Import String List Lia Nat.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Program.
From Coq Require Import Arith.Wf_nat.
From equivChecker Require Import utils operators pset syntax words semantics derivatives expr_deriv.
Import ListNotations.

(** * Improved Equivalence Checker *)

(**
  In the previous section, we defined a declarative (non-executable)
  algorithm for equivalence checking.
  Now the goal is to make it executable by choosing suitable datastructures
  and computations !

  Example : equations -> list of pairs
            derivation -> derivation on regular expressions
*)

Fixpoint final {A} (e : regexpr A) : bool :=
  match e with
  | Ezero => false
  | Eone => true
  | Echar a => false
  | Esum e1 e2 => final e1 || final e2
  | Ecat e1 e2 => final e1 && final e2
  | Estar e => true
  end.

Lemma empty_exp :
  forall {A} `{EQU: Equ A} (e : regexpr A),
    final e = true <-> lang_reg e [].
Proof.
  induction e.
  - easy.
  - repeat split. intros H. simpl in *. constructor. 
  - easy.
  - split.
    + intros H. simpl in H. 
      apply Bool.orb_prop in H.
      destruct H as [H1 |H2].
      * left. now apply IHe1.
      * right. now apply IHe2.
    + intros H. simpl in H. destruct H.
      * simpl. apply IHe1 in H. 
        apply Bool.orb_true_intro. now left.
      * simpl. apply IHe2 in H.
        apply Bool.orb_true_intro. now right.
  - split.
    + intros H. simpl in H.
      apply andb_prop in H as [H1 H2].
      simpl. apply IHe1 in H1. apply IHe2 in H2.
      exists [],[]. auto. easy.
    + intros H. simpl in H. destruct H as (w1 & w2 & H1 & H2 & H3).
      simpl. apply andb_true_intro.
      assert (w1 ≃ [] /\ w2 ≃ []) as [H4 H5].
      { rewrite H3. destruct w1; try easy. } 
      split. 
      * apply IHe1. now rewrite H4 in H1.
      * apply IHe2. now rewrite H5 in H2.
  - split. 
    + intros H. simpl.
      exists []. easy.  
    + now intros H. 
Qed.

Lemma empty_exp_not :
  forall {A} `{EQU: Equ A} (e : regexpr A),
    final e = false -> ~ (lang_reg e []).
Proof.
  induction e; try easy.
  - intros H H1. apply empty_exp in H1. now rewrite H in H1.
  - intros H H1. apply empty_exp in H1. now rewrite H in H1.
Qed.

(** ** Computing Normalized Derivatives *)
Fixpoint compute_regular_deriv {A} `{EquDec A} (a : A) (e : regexpr A) : regexpr A := 
  match e with 
  | Ezero => Ezero
  | Eone => Ezero
  | Echar b =>
      if equ_dec a b then Eone else Ezero
  | Esum e1 e2 =>
      (compute_regular_deriv a e1) ⊕ (compute_regular_deriv a e2)
  | Ecat e1 e2 =>
      if final e1 then 
        ((compute_regular_deriv a e1) ⊙ e2) ⊕ (compute_regular_deriv a e2)
      else
       (compute_regular_deriv a e1) ⊙ e2
  | Estar e => (compute_regular_deriv a e) ⊙ (Estar e)
  end.

Fixpoint compute_deriv {A} `{EquDec A} (a : A) (e : omega_regexpr A) : omega_regexpr A :=
  match e with
  | OEzero => OEzero
  | OEcat e_1 e_2 =>
    if final e_1 then
      mk_plus (mk_dot (compute_regular_deriv a e_1) e_2) (compute_deriv a e_2)
    else
      mk_dot (compute_regular_deriv a e_1) e_2
  | OEsum e_1 e_2 =>
      mk_plus (compute_deriv a e_1) (compute_deriv a e_2)
  | OEomega e => mk_dot (compute_regular_deriv a e) (OEomega e)
  end.

#[global]
Instance compute_regular_deriv_morphism_equ {A} `{EquDec A} : Proper (equ ==> equ ==> equ) (@compute_regular_deriv A _).
Proof.
  intros a b H1 e1 e2 H2. Opaque equ.
  induction H2; try easy.
  - simpl. destruct (equ_dec a a0) eqn: Hea, (equ_dec b b0) eqn: Heb; try easy.
    + exfalso. apply n. now rewrite <- H1, <- H0.
    + exfalso. apply n. now rewrite H1, H0.
  - simpl. now rewrite IHregexpr_equ_ind1, IHregexpr_equ_ind2.
  - simpl. destruct (final e1) eqn:F1, (final e3) eqn:F2.
    + now rewrite IHregexpr_equ_ind1, IHregexpr_equ_ind2, H2_0.
    + apply empty_exp in F1. rewrite H2_ in F1. apply empty_exp in F1.
      congruence.
    + apply empty_exp in F2. rewrite <- H2_ in F2. apply empty_exp in F2.
      congruence.
    + now rewrite IHregexpr_equ_ind1, H2_0.
  - simpl. now rewrite IHregexpr_equ_ind, H2.
Defined.

#[global]
Instance compute_deriv_morphism_equ {A} `{EquDec A} : Proper (equ ==> equ ==> equ) (@compute_deriv A _).
Proof.
  intros a b H1 e1 e2 H2.
  induction H2; try easy.
  - simpl. now rewrite IHomega_regexpr_equ_ind1, IHomega_regexpr_equ_ind2.
  - simpl. destruct (final e1) eqn:F1, (final e2) eqn:F2.
    + now rewrite IHomega_regexpr_equ_ind, H2, H1, H0.
    + apply empty_exp in F1. rewrite H0 in F1. apply empty_exp in F1. congruence.
    + apply empty_exp in F2. rewrite <- H0 in F2. apply empty_exp in F2. congruence.
    + now rewrite H0, H1, H2.
  - simpl. now rewrite H1, H0.
Defined.

Lemma flatten_help :
  forall {A} `{Equ A} (l : list (finword A)) (P : finword A -> Prop),
    ~ concat l ≃ [] /\ Forall P l -> exists a w l', Forall P ((a::w)::l') /\ concat l ≃ concat ((a::w)::l').
Proof.
  intros A EQU l P.
  induction l as [|w l IHl].
  - simpl in *. intros [H1 H2]. exfalso. now apply H1.
  - intros [H1 H2]. 
    destruct w.
    + simpl in *.
      destruct IHl as (a & w' & l' & IHl1 & IHl2).
      * split; try easy. now inversion H2.
      * exists a, w', l'. now split.
    + simpl in *. exists a, w, l. now split.
Qed.

Theorem compute_regular_deriv_correct {A} `{DEC: EquDec A} :
  forall (a : A) (e : regexpr A),
    lang_reg (compute_regular_deriv a e) ≃ δ(a, lang_reg e).
Proof.
  intros a e.
  induction e.
  - easy.
  - simpl. easy. 
  - simpl. split.
    + intros w H. unfold regular_deriv_a. unfold In, regular_deriv_a in *.
      destruct equ_dec.
      * destruct w.
        -- simpl. now constructor. 
        -- easy.
      * destruct w; try easy.
    + intros w H. unfold In, regular_deriv_a in *.
      destruct equ_dec.
      * destruct w. simpl. constructor. now inversion H.
      * destruct w; try easy.
        simpl. apply n. inversion H; eauto. now inversion H.
  - simpl. split.
    + intros w H. apply simpl_plus_reg_correct in H. destruct H.
      * left. destruct IHe1 as [H0 H1].
        now apply H0.
      * right. destruct IHe2 as [H0 H1].
        now apply H0.
    + intros w H. apply simpl_plus_reg_correct. destruct H. 
      * left. destruct IHe1 as [H0 H1].
        now apply H1.
      * right. destruct IHe2 as [H0 H1].
        now apply H1.
  - simpl. destruct (final e1) eqn:Feq.
    + simpl. split.
      * intros w H. unfold In in *. apply simpl_plus_reg_correct in H. destruct H.
        -- apply simpl_dot_reg_correct in H. destruct H as [w1 [w2 (H1 & H2 & H3)]].
           apply IHe1 in H1. unfold regular_deriv_a.
           unfold In, regular_deriv_a in H1.
           exists (a::w1). exists w2. 
           repeat split; try easy.
           simpl. now constructor.
        -- apply IHe2 in H. unfold In, regular_deriv_a in H|-*. 
           exists []. exists (a::w).
           repeat split; try easy.
           now apply empty_exp.
      * intros w H. unfold In in *. 
        unfold regular_deriv_a in H. destruct H as [w1 [w2 (H1 & H2 & H3)]].
        apply simpl_plus_reg_correct.
        destruct w1.
        -- right. apply IHe2. unfold In, regular_deriv_a. simpl in H3.
           now rewrite <- H3 in H2.
        -- assert (a ≃ a0).
           { simpl in H3. now inversion H3. }
           left. apply simpl_dot_reg_correct.
           exists w1, w2. repeat split.
           ++ destruct IHe1 as [H0 H0']. apply H0'.
              unfold In, regular_deriv_a. 
              assert (a::w1 ≃ a0::w1) by now constructor. now rewrite H4.
           ++ easy.
           ++ simpl in H3. now inversion H3.
    + simpl. split.
      * intros w H. unfold In, regular_deriv_a in H|-*.
        apply simpl_dot_reg_correct in H. destruct H as (w1 & w2 & H1 & H2 & H3).
        exists (a::w1), w2. repeat split; try easy.
        -- destruct IHe1 as [H0 H0']. now apply H0. 
        -- simpl. now constructor.
      * intros w H. unfold In, regular_deriv_a in H|-*.
        destruct H as (w1 & w2 & H1 & H2 & H3). apply simpl_dot_reg_correct.
        destruct w1, w2 eqn: Hw2; try easy; simpl in *.
        -- apply empty_exp in H1. now rewrite H1 in Feq.
        -- exists w1, [].
           repeat split; auto.
           ++ apply IHe1. unfold In, regular_deriv_a. 
              inversion H3; subst. rewrite <- app_nil_end in H7. 
              assert (a::w1 ≃ a0::w1) by now constructor. now rewrite H.
           ++ now inversion H3.
        -- exists w1, (a1::f).
           repeat split; auto. 
           ++ apply IHe1. unfold In, regular_deriv_a.
              inversion H3; subst.
              assert (a::w1 ≃ a0::w1) by now constructor. now rewrite H.
           ++ now inversion H3; subst.
  - simpl. split.
    + intros w H. unfold regular_deriv_a.
      apply simpl_dot_reg_correct in H.
      destruct H as [w1 [w2 (H1 & [l [H2 H3]] & H4)]].
      exists ((a::w1)::l). split.
      * apply IHe in H1. unfold regular_deriv_a in H1.
        now apply Forall_cons.
      * simpl. constructor; try easy. 
        rewrite H4. 
        assert (forall (w w1 w2 : finword A), w1 ≃ w2 -> w ++ w1 ≃ w ++ w2).
        { intros w0 w3 w4 He. induction w0; try easy.
          now constructor. }
        Transparent equ. now apply H.
    + intros w H. unfold regular_deriv_a in H.
      destruct H as (l & H1 & H2).
      destruct (flatten_help l (lang_reg e)) as (b & wb & l' & [H3 H4]).
      split; auto. now rewrite <- H2.
      apply simpl_dot_reg_correct.
      exists wb, (concat l').
      repeat split.
      * apply IHe. unfold In, regular_deriv_a.
        rewrite <- H2 in H4. clear H2.
        simpl in H4. inversion H4; subst. inversion H3; subst.
        assert (b :: wb ≃ a::wb). { constructor; try easy. }
        now rewrite <- H.
      * exists l'. split; auto. now inversion H3. reflexivity.
      * rewrite <- H2 in H4. clear H2.
        simpl in H4. now inversion H4; subst.
Qed.

Theorem compute_deriv_correct {A} `{EQUDEC : EquDec A} :
  forall (a : A) (e : omega_regexpr A),
    lang_omega_co (compute_deriv a e) ≃ Δ(a, lang_omega_co e).
Proof.
  intros a e.
  induction e.
  - easy.
  - simpl. split.
    + intros w H. apply simpl_plus_correct in H.
      unfold deriv_a.
      inversion H.
      * apply lang_omega_co_sum_l. 
        now apply IHe1.
      * apply lang_omega_co_sum_r.
        now apply IHe2.
    + intros w H. apply simpl_plus_correct.
      inversion H.
      * apply lang_omega_co_sum_l.
        now apply IHe1.
      * apply lang_omega_co_sum_r.
        now apply IHe2.
  - simpl. destruct (final r) eqn:Feq.
    + split.
      * intros w H. apply simpl_plus_correct in H. unfold deriv_a.
        apply empty_exp in Feq.
        inversion H.
        -- apply simpl_dot_correct in H3. inversion H3.
           apply compute_regular_deriv_correct in H6. unfold regular_deriv_a in H6.
           now eapply lang_omega_co_cat; eauto.
        -- apply IHe in H3. unfold deriv_a in H3.
           now eapply lang_omega_co_cat; eauto. 
      * intros w H. apply simpl_plus_correct. unfold deriv_a in H.
        inversion H.
        destruct w1.
        -- eapply lang_omega_co_sum_r.
           apply IHe. unfold deriv_a.
           now rewrite H5. 
        -- inversion H5.
           eapply lang_omega_co_sum_l. apply simpl_dot_correct. eapply lang_omega_co_cat.
           apply compute_regular_deriv_correct. unfold In, regular_deriv_a. exact H2.
           exact H3. easy.
    + split.
      * intros w H. apply simpl_dot_correct in H. unfold deriv_a.
        inversion H.
        apply compute_regular_deriv_correct in H2. unfold regular_deriv_a in H2.
        now eapply lang_omega_co_cat; eauto.
      * intros w H. apply simpl_dot_correct. unfold deriv_a in H.
        inversion H.
        assert (w1 <> []) as W1.
        { intros W. rewrite W in H2. apply empty_exp in H2. now rewrite H2 in Feq. } 
        destruct w1; try easy.
        eapply lang_omega_co_cat.
        apply compute_regular_deriv_correct. unfold regular_deriv_a.
        assert (a = a0) by now inversion H5.
        rewrite <- H6 in H2; eauto. exact H3. now inversion H5.
  - simpl. split.
    + intros w H. apply simpl_dot_correct in H. unfold deriv_a in *. 
      inversion H.
      apply compute_regular_deriv_correct in H2. unfold regular_deriv_a in H2.
      eapply lang_omega_co_omega; eauto; easy.
    + intros w H. apply simpl_dot_correct. unfold deriv_a in *.
      inversion H.
      destruct w1; try easy. inversion H4.
      eapply lang_omega_co_cat; eauto. 
      now apply compute_regular_deriv_correct. 
Qed.

(** ** Auxiliary Definitions *)

Fixpoint get {A} (i : nat) (w : coword A) : A :=
  match w with
  | lcons x w' => match i with 
    | 0 => x 
    | (S i) => get i w'
    end
  end.

#[global]
Instance get_morphism {A : Type} `{Equ A} : Proper (eq ==> equ ==> equ) (@get A).
Proof.
  intros i j H1. induction i in j,H1|-*; intros a b H2.
  - destruct j; try easy. destruct a, b. simpl. now inversion H2.
  - destruct j; try easy. destruct a, b. simpl.
    apply IHi. now inversion H1. now inversion H2.
Qed.


Fixpoint list_in {A} `{Equ A}  (e: A) (l : list A) : Prop := 
  match l with 
  | [] => False 
  | x::l => equ e x \/ list_in e l 
  end.

#[global]
Instance list_in_morphism {A : Type} `{Equ A} : Proper (equ ==> equ ==> iff) (@list_in A _).
Proof.
  intros a b Hab e1 e2 He.
  induction He; try easy.
  split.
  - intros H1. simpl in H1. destruct H1.
    + left. transitivity a; try easy. now transitivity x.
    + right. now rewrite <- IHHe.
  - intros H1. destruct H1.
    + left. transitivity b; try easy. now transitivity y.
    + right. now rewrite IHHe.
Qed.

Lemma in_app_or_equ {A} `{Equ A} :
  forall (l m : list A) (a : A),
       list_in a (l ++ m) -> list_in a l \/ list_in a m.
Proof.
  intros l m a. induction l.
  - simpl. intros H0. now right.
  - intros H0. destruct H0.
    + left. now left.
    + destruct (IHl H0).
      * left. now right.
      * now right.
Qed.

Lemma in_or_app_equ {A} `{Equ A} : 
  forall (l m : list A) (a : A),
       list_in a l \/ list_in a m -> list_in a (l ++ m).
Proof.
  intros l m a.
  induction l.
  - simpl. intros [H1|H2]; try easy.
  - intros [H1|H2].
    + destruct H1. 
      * now left.
      * right. apply IHl. now left.
    + right. apply IHl. now right.
Qed.

Definition MyMorphism {A B : Type} `{Equ A} `{Equ B} (f : A -> B) : Prop :=
  Proper (equ ==> equ) f.

Lemma in_map_iff_equ {A B : Type} `{Equ A} `{Equ B} (f : A -> B) `{Hf : MyMorphism f}:
 forall (l : list A) (y : B), list_in y (map f l) <-> (exists x : A, equ (f x) y /\ list_in x l).
Proof.
  intros l y.
  split.
  - induction l.
    + intros H1. easy.
    + intros H1. destruct H1. 
      * exists a. split; try easy. now left.
      * destruct (IHl H1) as [x [H2 H3]].
        exists x. split; try easy. now right.
  - induction l.   
    + intros [x [H1 H2]]. easy.
    + intros [x [H1 H2]]. destruct H2.
      * left. rewrite <- H1. now apply Hf. 
      * right. apply IHl. now exists x.
Qed.

Theorem existsb_exists_equ {A : Type} `{Equ A} : 
  forall (f : A -> bool) `{Hf : MyMorphism f} (l : list A), 
  existsb f l = true <-> (exists x : A, list_in x l /\ f x = true).
Proof.
  intros f Hf l. induction l.
  - simpl. split; try easy. intros [x [H1 H2]]; try easy.
  - split.
    + intros H1. simpl in H1. apply Bool.orb_true_elim in H1. destruct H1.
      * exists a. split; try easy. now left. 
      * rewrite IHl in e. destruct e as [b [H1 H2]].
        exists b. split; try easy. now right.
    + intros H1. destruct H1 as [b [H1 H2]].
      destruct H1.
      * simpl. apply Bool.orb_true_intro. left. rewrite <- H2. now apply Hf.
      * simpl. apply Bool.orb_true_intro. right. rewrite IHl.
        now exists b.
Qed.

Theorem forallb_forall_equ {A : Type} `{Equ A}  : 
  forall (f : A -> bool) `{Hf: MyMorphism f} (l : list A),
  forallb f l = true <-> (forall (x : A), list_in x l -> f x = true).
Proof.
  intros f Hf l. induction l.
  - easy.
  - split.
    + intros H1. simpl in H1. apply Bool.andb_true_iff in H1 as [H1 H2].
      intros x. intros H3. simpl in H3. destruct H3.
      * rewrite <- H1. now apply Hf.
      * now apply IHl.
    + intros H1. simpl. apply Bool.andb_true_iff. split.
      * apply H1. now left.
      * rewrite IHl. intros b H2.
        apply H1. now right.
Qed.

Theorem get_cat {A} `{EquDec A} (i : nat) (w1 : finword A) (w2 : coword A) :
  forall a, get i (w1 • w2) ≃ a -> list_in a w1 \/ exists j, get j w2 ≃ a.
Proof.
  intros a. induction w1 in i|-*.
  - simpl. intros H1. right. now exists i. 
  - intros H1. destruct (a0 =? a) eqn:Ha.
    + left. now left.
    + induction i; try easy. simpl in H1. 
      specialize (IHw1 i H1).
      destruct IHw1.
      * left. now right.
      * now right.
Qed.
Theorem get_cat' {A} `{EquDec A}(w1 : finword A) (w2 : coword A) :
  forall a, list_in a w1 -> exists j, get j (w1 • w2) ≃ a.
Proof.
  intros a. induction w1.
  - easy. 
  - intros [H1|H2].
    + now exists 0. 
    + specialize (IHw1 H2). destruct IHw1 as [j IH].
      now exists (S j).
Qed.

Class Finite (A : Type) `{Equ A} :=
{
  all_elem : list A;
  all_elem_correct: forall a, list_in a all_elem;
}.

(** ** Counterexample Detection Mechanism *) 

Fixpoint non_zero_regexp {A} (e : regexpr A) : bool := 
  match e with 
  | Ezero => false 
  | Eone => true 
  | Echar a => true
  | Esum e1 e2 => non_zero_regexp e1 || non_zero_regexp e2 
  | Ecat e1 e2 => non_zero_regexp e1 && non_zero_regexp e2 
  | Estar e => true
  end.

Fixpoint collect_alphabet_reg {A : Type} (e : regexpr A) : list A := 
  match e with 
  | Ezero => [] 
  | Eone => [] 
  | Echar a => [a]
  | Esum e1 e2 => collect_alphabet_reg e1 ++ collect_alphabet_reg e2 
  | Ecat e1 e2 => (*collect_alphabet_reg e1 ++ collect_alphabet_reg e2 *)
      if (non_zero_regexp e1 && non_zero_regexp e2)%bool then collect_alphabet_reg e1 ++ collect_alphabet_reg e2 else []
  | Estar e => collect_alphabet_reg e 
  end.

Fixpoint non_zero_omega_regexp {A} (e : omega_regexpr A) : bool := 
  match e with 
  | OEzero => false 
  | OEsum e1 e2 => non_zero_omega_regexp e1 || non_zero_omega_regexp e2 
  | OEcat e1 e2 => non_zero_regexp e1 && non_zero_omega_regexp e2 
  | OEomega e => match collect_alphabet_reg e with 
                 | [] => false 
                 | _ => true
                 end
  end.

Fixpoint collect_alphabet {A : Type} (e : omega_regexpr A) : list A :=
  match e with 
  | OEzero => [] 
  | OEsum e1 e2 => collect_alphabet e1 ++ collect_alphabet e2 
  | OEcat e1 e2 => (* collect_alphabet_reg e1 ++ collect_alphabet e2 *)
      if (non_zero_regexp e1 && non_zero_omega_regexp e2)%bool then collect_alphabet_reg e1 ++ collect_alphabet e2 else []
  | OEomega e => collect_alphabet_reg e 
  end.

(** *** Unequal Alphabet Checker *)
Definition unequal_alphabet {A : Type} `{EquDec A} (e1 e2 : omega_regexpr A) : bool :=
  let l1 := collect_alphabet e1 in
  let l2 := collect_alphabet e2 in
  (
    existsb (fun a =>
      forallb (fun b =>
        if a =? b then false else true
      ) l2
    ) l1 || 
    existsb (fun a =>
      forallb (fun b =>
        if a =? b then false else true
      ) l1
    ) l2
  ).

Inductive NonZero {A} : regexpr A -> Prop :=
  | nonzero_one : NonZero Eone
  | nonzero_char a : NonZero (Echar a)
  | nonzero_sum_l e1 e2 : NonZero e1 -> NonZero (Esum e1 e2)
  | nonzero_sum_r e1 e2 : NonZero e2 -> NonZero (Esum e1 e2)
  | nonzero_cat e1 e2 : NonZero e1 -> NonZero e2 -> NonZero (Ecat e1 e2)
  | nonzero_star e : NonZero (Estar e).

Inductive Contains {A} `{Equ A} (a : A) : regexpr A -> Prop :=
  | contains_char b :  a ≃ b -> Contains a (Echar b)
  | contains_sum_l e1 e2 : Contains a e1 -> Contains a (Esum e1 e2)
  | contains_sum_r e1 e2 : Contains a e2 -> Contains a (Esum e1 e2)
  | contains_cat_l e1 e2 : Contains a e1 -> NonZero e2 -> Contains a (Ecat e1 e2)
  | contains_cat_r e1 e2 : Contains a e2 -> NonZero e1 -> Contains a (Ecat e1 e2)
  | contains_star e : Contains a e -> Contains a (Estar e).

Inductive NonZeroOmega {A} `{Equ A} : omega_regexpr A -> Prop := 
  | nonzeroomega_sum_l e1 e2 : NonZeroOmega e1 -> NonZeroOmega (OEsum e1 e2)
  | nonzeroomega_sum_r e1 e2 : NonZeroOmega e2 -> NonZeroOmega (OEsum e1 e2)
  | nonzeroomega_cat e1 e2 : NonZero e1 -> NonZeroOmega e2 -> NonZeroOmega (OEcat e1 e2)
  | nonzeroomega_omega e a : Contains a e -> NonZeroOmega (OEomega e).

Inductive ContainsOmega {A} `{Equ A} (a : A) : omega_regexpr A -> Prop := 
  | contains_osum_l e1 e2 : ContainsOmega a e1 -> ContainsOmega a (OEsum e1 e2) 
  | contains_osum_r e1 e2 : ContainsOmega a e2 -> ContainsOmega a (OEsum e1 e2)
  | contains_ocat_l e1 e2 : Contains a e1 -> NonZeroOmega e2 -> ContainsOmega a (OEcat e1 e2) 
  | contains_ocat_r e1 e2 : ContainsOmega a e2 -> NonZero e1 -> ContainsOmega a (OEcat e1 e2) 
  | contains_omega e : Contains a e -> ContainsOmega a (OEomega e).

Lemma NonZero_contains :
  forall A `{EQU : Equ A} (e : regexpr A),
    NonZero e <-> exists w, lang_reg e w.
Proof.
  intros A Hequ e. split.
  + induction 1.
    - now repeat econstructor.
    - now repeat econstructor.
    - destruct IHNonZero as [w Hw].
      exists w. now left.
    - destruct IHNonZero as [w Hw].
      exists w. now right.
    - destruct IHNonZero1 as [w1 Hw1].
      destruct IHNonZero2 as [w2 Hw2].
      now exists (w1 ++ w2), w1, w2.
    - exists []. now econstructor.
  + induction e; try easy.
    - intros [w H]. destruct H.
    - intros [w H]. constructor.
    - intros [w H]. constructor.
    - intros [w H]. destruct H.
      * constructor. apply IHe1. now exists w.
      * apply nonzero_sum_r. apply IHe2. now exists w.
    - intros [w H]. destruct H as (w1 & w2 & H1 & H2 & H3).
      constructor. 
      * apply IHe1. now exists w1.
      * apply IHe2. now exists w2.
    - intros [w H]. now constructor.
Qed.

Inductive non_empty {A} : list A -> Type :=
  | non_empty_wit (a : A) (l : list A) : non_empty (a::l).

CoFixpoint cons_repeat {A} (w1 w2 : finword A) (Hw2 : non_empty w2) : coword A :=
  match w1 with
  | [] => 
    match Hw2 with
    | non_empty_wit a l => a :? cons_repeat l w2 Hw2
    end
  | x::xs =>
    x :? cons_repeat xs w2 Hw2
  end.

Theorem cons_repeat_correct {A : Type} `{Equ A} :
  forall (w1 w2 : finword A) Hw2,
    cons_repeat w1 w2 Hw2 ≃ w1 • cons_repeat w2 w2 Hw2.
Proof.
  induction w1; intros.
  - simpl. destruct Hw2.
    rewrite force_id at 1. simpl.
    rewrite force_id. simpl.
    reflexivity.
  - simpl. destruct Hw2.
    rewrite force_id at 1. simpl.
    rewrite force_id. simpl.
    econstructor. apply IHw1.
Defined.

Definition repeat_word {A} (w : finword A) (Hw : non_empty w) :=
  cons_repeat w w Hw.

Theorem repeat_word_correct {A : Type} `{Equ A} :
  forall (w : finword A) Hw, repeat_word w Hw ≃ w • repeat_word w Hw.
Proof.
  intros w Hw.
  unfold repeat_word. now apply cons_repeat_correct.
Qed.

Lemma contains_non_zero_reg : 
  forall A `{EQU : Equ A} a (e : regexpr A),
  Contains a e -> NonZero e.
Proof.
  intros A E a e H. induction H; now constructor.
Qed.

Lemma contains_non_zero_omega : 
  forall A `{EQU : Equ A} a (e : omega_regexpr A),
  ContainsOmega a e -> NonZeroOmega e.
Proof.
  intros A E a e H. induction H; try now constructor.
  - apply nonzeroomega_cat; try easy. eapply contains_non_zero_reg; eauto.
  - econstructor; eauto. 
Qed.

Lemma Contains_word :
  forall A `{EQU : Equ A} a (e : regexpr A),
    Contains a e <-> exists w, lang_reg e w /\ list_in a w.
Proof.
  intros. split.
  - induction 1.
    + exists [a].
      now repeat econstructor.
    + destruct IHContains as [w [H1 H2]].
      exists w. split; try easy.
      now constructor.
    + destruct IHContains as [w [H1 H2]].
      exists w. split; try easy.
      now constructor 2.
    + destruct IHContains as [w [Hw_1 Hw_2]].
      pose proof (NonZero_contains _ e2) as [Hw1  Hw2].
      apply Hw1 in H0. destruct H0 as [w2 H0].
      exists (w ++ w2); split.
      now exists w, w2.
      apply in_or_app_equ. now left.
    + destruct IHContains as [w [Hw_1 Hw_2]].
      pose proof (NonZero_contains _ e1) as [Hw1 Hw2].
      apply Hw1 in H0. destruct H0 as [w2 H0].
      exists (w2 ++ w); split.
      now exists w2, w.
      apply in_or_app_equ. now right.
    + destruct IHContains as [w [H1 H2]].
      exists w. split; try easy.
      exists [w]. split; try repeat constructor; try easy.
      simpl. now rewrite app_nil_r. 
  - induction e; intros [w [H1 H2]]; try easy.
    + simpl in H1. inversion H1. now rewrite <- H in H2.
    + constructor. inversion H1; subst.
      destruct w1; try easy. inversion H2; try easy.
      now transitivity x.
    + destruct H1.
      * constructor. apply IHe1. now exists w.
      * apply contains_sum_r. apply IHe2. now exists w.
    + destruct H1 as (w1 & w2 & H1 & H3 & H4).
      rewrite H4 in H2. apply in_app_or_equ in H2. destruct H2.
      * constructor. apply IHe1. exists w1; try easy.
        eapply NonZero_contains. now exists w2.
      * apply contains_cat_r. apply IHe2. exists w2; try easy.
        eapply NonZero_contains. now exists w1.
    + constructor. Opaque equ. simpl in H1.
      destruct H1 as (l & H1 & H3).
      destruct w; try easy.
      rewrite H3 in H2. clear H3. 
      induction l.
      * easy. 
      * simpl in H2. apply in_app_or_equ in H2. destruct H2.
        -- apply IHe. exists a1. split; try easy. now inversion H1.
        -- apply IHl; try easy. now inversion H1.
Qed.

Lemma lang_omega_co_repeat:
  forall {A} `{EQU : Equ A} e w (Hw : non_empty w), lang_reg e w -> lang_omega_co (OEomega e) (repeat_word w Hw).
Proof.
  intros.
  assert (Hnil : w <> []) by now destruct w.
  cofix IH.
  apply (lang_omega_co_omega w (repeat_word w Hw) _ _ Hnil H IH).
  clear IH.
  apply repeat_word_correct.
Qed.

Lemma NonZeroOmega_contains :
  forall A `{EQU : Equ A} (e : omega_regexpr A),
    NonZeroOmega e <-> exists w, lang_omega_co e w.
Proof.
  intros A Hequ e. split.
  - intros H. induction H.
    + destruct IHNonZeroOmega as [w IH].
      exists w. now constructor.
    + destruct IHNonZeroOmega as [w IH].
      exists w. now constructor 2.
    + destruct IHNonZeroOmega as [w IH].
      apply (@NonZero_contains A Hequ) in H. destruct H as [w' H].
      exists (w' • w). eapply lang_omega_co_cat.
      exact H. exact IH. reflexivity.
    + apply (Contains_word) in H.
      destruct H as [w [H1 H2]].
      assert (Hw : non_empty w) by (destruct w; try easy).
      eexists (repeat_word w Hw). now apply lang_omega_co_repeat.
  - induction e.
    + intros [w H]. destruct w; try easy.
    + intros [w H]. inversion H; subst.
      * constructor. apply IHe1. now exists w.
      * constructor 2. apply IHe2. now exists w.
    + intros [w H]. inversion H; subst. 
      constructor. rewrite (@NonZero_contains A Hequ).
      now exists w1.
      apply IHe. now exists w2.
    + intros [w H]. destruct w; try easy.
      apply (nonzeroomega_omega _ x).
      inversion H; subst.
      apply Contains_word. exists w1.
      split; auto. destruct w1; try easy.
      inversion H4; subst. now left.
Qed.

Inductive SliceAt {A : Type} `{Equ A} (e : regexpr A) : coword A -> nat -> finword A -> Prop := 
  | slice_now w n w1 w2 : 
      w ≃ w1 • w2 -> lang_reg e w1 -> n < length w1 -> SliceAt e w n w1 
  | slice_later w n w1 w2 w3: 
      w ≃ w1 • w2 -> lang_reg e w1 -> n >= length w1 -> 
      SliceAt e w2 (n - length w1) w3 -> SliceAt e w n w3.

Theorem omega_to_sliceAt {A : Type} `{Hequ: Equ A} : 
  forall (e : regexpr A) (n : nat) (w : coword A), 
    lang_omega_co (OEomega e) w -> exists wf, SliceAt e w n wf.
Proof.
  intros e n.
  induction n using (well_founded_induction lt_wf).
  intros w H1. inversion H1; subst.
  destruct (PeanoNat.Nat.lt_ge_cases n (length w1)).
  - exists w1. eapply slice_now.
    exact H5. exact H3. exact H0.
  - assert (n - length w1 < n) as Hl.
    { destruct w1; try easy. simpl in *. lia. }
    specialize (H (n - length w1) Hl w2 H4). destruct H as [wf H].
    exists wf. eapply slice_later.
    exact H5. exact H3. lia. exact H.
Qed.

Theorem sliceAt_to_lang_reg {A : Type} `{Hequ: Equ A} : 
  forall (e : regexpr A) w i wf, SliceAt e w i wf -> lang_reg e wf.
Proof.
  intros e w i wf H. induction H.
  - exact H0.
  - exact IHSliceAt.
Qed.

Lemma length_get {A : Type} `{Hequ: Equ A} : 
  forall  (w1 : finword A) w2 i , i < length w1 -> list_in (get i (w1 • w2)) w1.
Proof.
  intros w1. induction w1; try easy.
  intros w2 i H.
  destruct i.
  - simpl. now left.
  - simpl. right. apply IHw1.
    simpl in H. lia.
Qed.

Lemma length_get_2 {A : Type} `{Hequ: Equ A} : 
  forall i (w1 : finword A) w2 w3, i >= length w1 -> list_in (get (i - length w1) w2) w3 -> list_in (get i (w1 • w2)) w3.
Proof.
  induction i.
  - intros. destruct w1; try easy. 
  - intros. destruct w1; try easy.
    simpl in *. apply IHi; try easy. lia.
Qed.

Theorem sliceAt_to_in {A : Type} `{Hequ: Equ A} : 
  forall (e : regexpr A) w i wf, SliceAt e w i wf -> list_in (get i w) wf.
Proof.
  intros e w i wf H. induction H.
  - rewrite H. eapply length_get in H1; eauto.
  - rewrite H. now apply length_get_2.
Qed.

Theorem omega_contains_word_i {A : Type} `{Hequ: Equ A} : 
  forall (e : regexpr A) w a,
    lang_omega_co (OEomega e) w -> (exists i, get i w ≃ a) -> 
      exists w', lang_reg e w' /\ list_in a w'.
Proof.
  intros e w a H1 [i H2]. 
  pose proof (omega_to_sliceAt e i w H1) as [wf H3].
  exists wf. split.
  - eapply sliceAt_to_lang_reg; eauto.
  - rewrite <- H2. eapply sliceAt_to_in; eauto.
Qed.

Lemma Contains_omega_word :
  forall A `{EQU : EquDec A} a (e : omega_regexpr A),
    ContainsOmega a e <-> exists w, lang_omega_co e w /\ exists i, get i w ≃ a.
Proof.
  intros A Hequ a e. split.
  - intros H. induction H.
    + destruct IHContainsOmega as (w & H1 & H2).
      exists w. split; try easy. now constructor.
    + destruct IHContainsOmega as (w & H1 & H2).
      exists w. split; try easy. now constructor 2.
    + apply Contains_word in H as (w1 & H1 & H2).
      eapply (@NonZeroOmega_contains A) in H0 as (w2 & H3).
      exists (w1 • w2). split.
      * econstructor; eauto. reflexivity.
      * clear H1. induction w1; try easy.
        destruct (a =? a0) eqn:Ha.
        -- now exists 0. 
        -- destruct H2; try easy. specialize (IHw1 H).
           destruct IHw1 as [i IH].
           now exists (S i). 
    + destruct IHContainsOmega as (w & H1 & H2).
      eapply (@NonZero_contains A) in H0 as (w2 & H0).
      exists (w2 • w). split.
      * econstructor. exact H0. exact H1. reflexivity.
      * destruct H2 as [i H2]. 
        exists (length w2 + i)%nat. 
        clear H0. induction w2; try easy.
    + apply Contains_word in H as (w & H1 & H2).
      assert (Hw : non_empty w) by now destruct w.
      eexists (repeat_word w Hw). split.
      now apply lang_omega_co_repeat.
      pose proof (@get_cat' A Hequ w (repeat_word w Hw) a H2) as [j Hj].
      exists j. now rewrite repeat_word_correct.
  - induction e; try easy.
    + now intros [w [H1 H2]].
    + intros [w [H1 H2]]. inversion H1; subst.
      * constructor. apply IHe1. now exists w.
      * constructor 2. apply IHe2. now exists w.
    + intros [w [H1 H2]]. inversion H1; subst.
      destruct H2 as [i H2]. 
      rewrite H6 in H2. apply get_cat in H2. destruct H2.
      * constructor. 
        apply Contains_word. now exists w1.
        pose proof (@NonZeroOmega_contains A _). rewrite H0. now exists w2.
      * apply contains_ocat_r.
        apply IHe. exists w2. split; try easy.
        pose proof (@NonZero_contains A _). rewrite H0. now exists w1.
    + intros [w [H1 H2]]. constructor.
      apply Contains_word. eapply omega_contains_word_i; eauto.
Qed.

Theorem non_zero_equ_regexp {A} : 
  forall (e : regexpr A), NonZero e <-> non_zero_regexp e = true.
Proof.
  intros e. split.
  - intros H. induction H; try easy.
    + simpl. apply Bool.orb_true_intro.
      now left.
    + simpl. apply Bool.orb_true_intro.
      now right.
    + simpl. apply Bool.andb_true_iff.
      now split.
  - induction e; intros H; try easy.
    + constructor.
    + constructor.
    + simpl in H. apply Bool.orb_true_elim in H.
      destruct H as [H|H].
      * econstructor. now apply IHe1.
      * apply nonzero_sum_r. now apply IHe2.
    + simpl in H. apply Bool.andb_true_iff in H as [H1 H2].
      constructor.
      now apply IHe1. now apply IHe2.
    + simpl in H. constructor. 
Qed.

Theorem contains_collect_regexp {A} `{Equ A} : 
  forall (a : A) (e : regexpr A), Contains a e <-> list_in a (collect_alphabet_reg e).
Proof.
  intros a e. split.
  - intros H1. induction H1; try easy.
    + simpl. now left.
    + simpl. apply in_or_app_equ. now left.
    + simpl. apply in_or_app_equ. now right.
    + simpl. apply non_zero_equ_regexp in H0.
      apply contains_non_zero_reg, non_zero_equ_regexp in H1. rewrite H1, H0. 
      apply in_or_app_equ. now left.
    + simpl. apply contains_non_zero_reg in H1.
      apply non_zero_equ_regexp in H0, H1. rewrite H0, H1.
      apply in_or_app_equ. now right.
  - induction e; try easy.
    + intros H1. simpl in *. destruct H1; try easy. now constructor.
    + intros H1. simpl in *. apply in_app_or_equ in H1. destruct H1.
      * constructor. now apply IHe1.
      * apply contains_sum_r. now apply IHe2.
    + intros H1. simpl in H1. 
      destruct (non_zero_regexp e1) eqn:N1, (non_zero_regexp e2) eqn:N2; try easy.
      simpl in H1. apply in_app_or_equ in H1. destruct H1.
      * constructor. now apply IHe1. now apply non_zero_equ_regexp.
      * apply contains_cat_r. now apply IHe2. now apply non_zero_equ_regexp.
    + intros H1. simpl in H1. constructor. now apply IHe.
Qed.

Theorem non_zero_equ_omega_regexp {A} `{Hequ : Equ A} : 
  forall (e : omega_regexpr A), NonZeroOmega e <-> non_zero_omega_regexp e = true.
Proof.
  intros e. split.
  - intros H. induction H; try easy.
    + simpl. apply Bool.orb_true_intro. now left.
    + simpl. apply Bool.orb_true_intro. now right.
    + simpl. apply Bool.andb_true_iff. split; try easy.
      now apply non_zero_equ_regexp.
    + simpl. apply contains_collect_regexp in H. 
      destruct (collect_alphabet_reg e); try easy. 
  - intros H. induction e; try easy.
    + simpl in H. apply Bool.orb_true_elim in H.
      destruct H.
      * constructor. now apply IHe1.
      * constructor 2. now apply IHe2.
    + simpl in H. apply Bool.andb_true_iff in H as [H1 H2].
      constructor. 
      * now apply non_zero_equ_regexp.
      * now apply IHe.
    + simpl in H. destruct (collect_alphabet_reg r) eqn:C; try easy.
      econstructor. apply contains_collect_regexp. rewrite C. now left.
Qed.

Theorem contains_collect_omega_regexp {A} `{Equ A} : 
  forall (a : A) (e : omega_regexpr A), ContainsOmega a e <-> list_in a (collect_alphabet e).
Proof.
  intros a e. split.
  - intros H1. induction H1.
    + simpl. apply in_or_app_equ. now left.
    + simpl. apply in_or_app_equ. now right.
    + simpl. destruct (non_zero_regexp e1) eqn:N1, (non_zero_omega_regexp e2) eqn:N2.
      * apply in_or_app_equ. left. now apply contains_collect_regexp.
      * apply non_zero_equ_omega_regexp in H1. congruence.
      * apply contains_non_zero_reg, non_zero_equ_regexp in H0. congruence.
      * apply non_zero_equ_omega_regexp in H1. congruence.
    + simpl. destruct (non_zero_regexp e1) eqn:N1, (non_zero_omega_regexp e2) eqn:N2.
      * apply in_or_app_equ. now right.
      * apply contains_non_zero_omega, non_zero_equ_omega_regexp in H1. congruence.
      * apply non_zero_equ_regexp in H0. congruence.
      * apply non_zero_equ_regexp in H0. congruence.
    + simpl. now apply contains_collect_regexp.
  - induction e; try easy.
    + intros H1. simpl in H1. apply in_app_or_equ in H1. destruct H1.
      * constructor. now apply IHe1.
      * constructor 2. now apply IHe2.
    + intros H1. simpl in H1. 
      destruct (non_zero_regexp r) eqn:N1, (non_zero_omega_regexp e) eqn:N2; try easy.
      apply in_app_or_equ in H1. destruct H1.
      * constructor. now apply contains_collect_regexp.
        now apply non_zero_equ_omega_regexp.
      * apply contains_ocat_r. now apply IHe.
        now apply non_zero_equ_regexp.
    + intros H1. simpl in H1.
      constructor. now apply contains_collect_regexp.
Qed.

(** *** Correctness *)
Theorem unequal_alphabet_not_equivalent {A} `{D : EquDec A} `{F: @Finite A (@equ_dec_equ _ D)}:
  forall e1 e2, unequal_alphabet e1 e2 = true -> ~ lang_omega_co e1 ≃ lang_omega_co e2.
Proof.
  intros e1 e2 H.
  unfold unequal_alphabet in H.
  apply Bool.orb_true_elim in H. destruct H as [H3|H3].
  - apply existsb_exists_equ in H3. destruct H3 as [a [H3 H4]].
    rewrite forallb_forall_equ in H4. 
    rewrite <- contains_collect_omega_regexp in H3.
    rewrite Contains_omega_word in H3. destruct H3 as [w [H3 H3']].
    intros H. apply H in H3.
    pose proof (Contains_omega_word _ a e2).
    specialize (H4 a). 
    rewrite <- contains_collect_omega_regexp in H4. 
    enough ((if a =? a then false else true) = true).
    destruct (a =? a); try easy. now apply n.
    apply H4. apply H0. now exists w.
    + intros b c H. destruct (a =? b), (a =? c); try easy.
      exfalso. apply n. now transitivity b.
      exfalso. apply n. now transitivity c.
    + intros b c Hbc. Transparent equ. simpl. clear - Hbc.
      induction (collect_alphabet e2); try easy.
      simpl. destruct (b =? a) eqn:Hba, (c =? a) eqn:Hca; try easy.
      * exfalso. apply n. now transitivity b.
      * exfalso. apply n. now transitivity c.
  - apply existsb_exists_equ in H3. destruct H3 as [a [H3 H4]].
    rewrite forallb_forall_equ in H4. 
    rewrite <- contains_collect_omega_regexp in H3.
    rewrite Contains_omega_word in H3. destruct H3 as [w [H3 H3']].
    intros H. apply H in H3.
    pose proof (Contains_omega_word _ a e1).
    specialize (H4 a). 
    rewrite <- contains_collect_omega_regexp in H4. 
    enough ((if a =? a then false else true) = true).
    destruct (a =? a); try easy. now apply n.
    apply H4. apply H0. now exists w.
    + intros b c H. destruct (a =? b), (a =? c); try easy.
      exfalso. apply n. now transitivity b.
      exfalso. apply n. now transitivity c.
    + intros b c Hbc. Transparent equ. simpl. clear - Hbc.
      induction (collect_alphabet e1); try easy.
      simpl. destruct (b =? a) eqn:Hba, (c =? a) eqn:Hca; try easy.
      * exfalso. apply n. now transitivity b.
      * exfalso. apply n. now transitivity c.
Qed.

(** *** Trivially not Equivalent Function *)
Definition trivially_not_equal {A} `{EquDec A} `{Finite A} (e1 : omega_regexpr A) (e2 : omega_regexpr A) : bool :=
  unequal_alphabet e1 e2.

Theorem lang_trivially_not_omega_regexp {A} `{D : EquDec A} `{F: @Finite A (@equ_dec_equ _ D)}:
  forall e1 e2, trivially_not_equal e1 e2 = true -> ~ lang_omega_co e1 ≃ lang_omega_co e2.
Proof.
  unfold trivially_not_equal.
  exact unequal_alphabet_not_equivalent.
Qed.

(** ** Equivalence Checker *)

Definition ListEquations A := list (omega_regexpr A * omega_regexpr A).

Inductive algo_option (A : Type) : Type  := 
  | FINISHED : algo_option A
  | CLASH : A -> algo_option A
  | CONTINUE : A -> algo_option A. 
Arguments FINISHED {_}.
Arguments CLASH {_}.
Arguments CONTINUE {_}.

(* Step of Algorithm *)
Definition algo_step {A} `{EquDec A} `{Finite A} (l : ListEquations A) : ListEquations A :=
  match l with 
  | [] => []
  | (e1, e2)::l' =>
    if equ_dec e1 e2 then l' else
        let d := map (fun a => (compute_deriv a e1, compute_deriv a e2)) all_elem in
        l' ++ d
  end.

Definition ValidList {A} `{Equ A} (E : ListEquations A) :=
  forall e1 e2, list_in (e1, e2) E -> lang_omega_co e1 ≃ lang_omega_co e2.

Definition equivList {A} `{Equ A} (E E' : ListEquations A) :=
  ValidList E <-> ValidList E'.


Theorem algo_step_sound:
  forall {A} (DEC : EquDec A) (HF : @Finite A (@equ_dec_equ _ DEC)) (l1 l2 : ListEquations A),
    algo_step l1 = l2 -> equivList l1 l2.
Proof.
  intros A HD HF l1 l2 H. split.
  - intros H1. rewrite <- H.
    unfold ValidList in *.
    destruct l1; try easy. destruct p as [e1 e2].
    unfold algo_step. destruct (e1 =? e2) eqn:EQ.
    + intros e3 e4 H2. apply H1. now right.
    + intros e3 e4 H2. 
      apply in_app_or_equ in H2. destruct H2 as [H3|H3].
      * apply H1. now right.
      * apply in_map_iff_equ in H3. destruct H3 as [a [H3 H3']].
        destruct H3 as [<- <-].
        -- rewrite compute_deriv_correct, compute_deriv_correct.
           pose proof (@deriv_eq A) as [DQ1 DQ2]. apply DQ1.
           apply H1. now left.
        -- intros x y Hxy. split; now rewrite Hxy.
  - intros H1. unfold ValidList in *.
    destruct l1; try easy. destruct p as [e1 e2].
    unfold algo_step in H. destruct (e1 =? e2) eqn: Eq.
    + intros e3 e4 H3. destruct H3 as [H3|H3].
      * inversion H3 as [-> ->]. now rewrite e. 
      * apply H1. now rewrite <- H.
    + intros e3 e4 H3. destruct H3 as [H3|H3].
      * apply deriv_eq. intros a.
        rewrite <- compute_deriv_correct, <- compute_deriv_correct.
        apply H1. rewrite <- H.
        apply in_or_app_equ. right. apply in_map_iff_equ.
        -- intros x y Hxy. split; now rewrite Hxy.
        -- exists a. split.
           constructor; inversion H3. now rewrite H0. now rewrite H2.
           apply all_elem_correct.
      * apply H1. rewrite <- H.
        apply in_or_app_equ. now left.
Qed.

(** Steps of Algorithm *)
CoFixpoint run_algo {A} `{EquDec A} `{Finite A} (l : ListEquations A) : coword (ListEquations A) :=
  lcons l (run_algo (algo_step l)).

Theorem run_algo_sound:
  forall {A} (DEC : EquDec A) (HF : @Finite A (@equ_dec_equ _ DEC)) (l1 l2 : ListEquations A) i,
    get i (run_algo l1) = l2 -> equivList l1 l2.
Proof.
  intros A HD HF l1 l2 i. 
  induction i in l1 |-*.
  - simpl. intros H. now rewrite H.
  - intros H. simpl in H.
    pose proof (@algo_step_sound A) as H2.
    specialize (IHi _ H).
    specialize (H2 _ _ l1 _ eq_refl).
    unfold equivList in *.
    now rewrite H2.
Qed.

(** *** Observe Function *)
CoFixpoint observe {A} `{DEC : EquDec A} {F: @Finite A (@equ_dec_equ _ DEC)} (s : coword (ListEquations A)) : coword (algo_option (ListEquations A)) := 
  match s with 
  | l :? s => let r := match l with 
                       | [] => FINISHED
                       | (e1,e2)::l' => if trivially_not_equal e1 e2 then CLASH [(e1, e2)]
                                        else CONTINUE l 
                       end
              in
                r :? observe s 
  end.

(** *** Soundness *)
Lemma observe_algo_finished :
  forall {A} (DEC : EquDec A) (HF : @Finite A (@equ_dec_equ _ DEC)) (l : ListEquations A) i,
    get i (run_algo l) = [] <-> get i (observe (run_algo l)) = FINISHED.
Proof.
  intros. split.
  + intros H.
    induction i in l,H|-*.
    - simpl in *. rewrite H. reflexivity.
    - simpl. simpl in H. now apply IHi.
  + intros H.
    induction i in l,H|-*.
    - simpl in *. destruct l; try easy. 
      destruct p as [e1 e2]. destruct (trivially_not_equal e1 e2); try easy.
    - simpl in *. now apply IHi.
Qed.

Theorem observe_sound_finished : 
  forall {A} (DEC : EquDec A) (HF : @Finite A (@equ_dec_equ _ DEC)) (l1 : ListEquations A) i,
    get i (observe (run_algo l1)) = FINISHED -> equivList l1 [].
Proof.
  intros A D F l i H. 
  apply observe_algo_finished in H.
  eapply run_algo_sound; eauto.
Qed.

Theorem observe_sound_clash : 
  forall {A} (DEC : EquDec A) (HF : @Finite A (@equ_dec_equ _ DEC)) (l1 l2 : ListEquations A) i,
    get i (observe (run_algo l1)) = CLASH l2 -> ~ ValidList l1.
Proof.
  intros A D F l1 l2 i H.
  induction i in l1,l2,H|-*.
  - simpl in *. destruct l1; try easy. destruct p as [e1 e2].
    destruct (trivially_not_equal e1 e2) eqn:T; try easy.
    apply lang_trivially_not_omega_regexp in T.
    intros H1. apply T. apply H1. now left.
  - simpl in *. 
    pose proof (@algo_step_sound A).
    intros H1.
    eapply (IHi (algo_step l1)).
    exact H. 
    specialize (H0 _ _ l1 (algo_step l1) eq_refl). destruct H0 as [H0 H0']. 
    now apply H0.
Qed.

Theorem observe_sound_equal : 
  forall {A} (DEC : EquDec A) (HF : @Finite A (@equ_dec_equ _ DEC)) (e1 e2 : omega_regexpr A) i,
    get i (observe (run_algo [(e1,e2)])) = FINISHED -> lang_omega_co e1 ≃ lang_omega_co e2.
Proof.
  intros A D F e1 e2 i H.
  apply observe_sound_finished in H.
  apply H; try easy. now left.
Qed.

Theorem observe_sound_not_equal : 
  forall {A} (DEC : EquDec A) (HF : @Finite A (@equ_dec_equ _ DEC)) (e1 e2 : omega_regexpr A) l i,
    get i (observe (run_algo [(e1,e2)])) = CLASH l -> ~ (lang_omega_co e1 ≃ lang_omega_co e2).
Proof.
  intros A D F e1 e2 i l H.
  apply observe_sound_clash in H.
  intros H1. apply H. intros e3 e4 H2.
  destruct H2; try easy. now inversion H0 as [-> ->].
Qed.

Theorem observe_sound_continue : 
  forall {A} (DEC : EquDec A) (HF : @Finite A (@equ_dec_equ _ DEC)) (l1 l2 : ListEquations A) i,
    get i (observe (run_algo l1)) = CONTINUE l2 -> equivList l1 l2.
Proof.
  intros A D F l1 l2 i H.
  induction i in l1,l2,H|-*.
  - simpl in *. destruct l1; try easy.
    destruct p as [e1 e2]. destruct (trivially_not_equal e1 e2); try easy.
    now inversion H.
  - simpl in *.
    pose proof (@algo_step_sound A). specialize (H0 _ _ l1 (algo_step l1) eq_refl).
    specialize (IHi (algo_step l1) l2 H).
    destruct IHi as [H1 H2]. destruct H0 as [H3 H4]. split.
    + intros H0. now apply H1, H3.
    + intros H0. now apply H4, H2.
Qed.

