From Coq Require Import String List Lia.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Program.
From equivChecker Require Import utils operators pset syntax words semantics derivatives.
Import ListNotations.

(** * Naive Equivalence Checker *)

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

(** ** Computing Derivatives *)
Fixpoint compute_regular_deriv {A} `{EquDec A} (a : A) (r : regexpr A) : regexpr A := 
  match r with 
  | Ezero => Ezero
  | Eone => Ezero
  | Echar b =>
      if equ_dec a b then Eone else Ezero
  | Esum r1 r2 =>
    Esum (compute_regular_deriv a r1) (compute_regular_deriv a r2)
  | Ecat r1 r2 =>
      if final r1 then 
        (Ecat (compute_regular_deriv a r1) r2) + compute_regular_deriv a r2
      else
       Ecat (compute_regular_deriv a r1) r2
  | Estar r => Ecat (compute_regular_deriv a r) (Estar r)
  end.

Fixpoint compute_deriv {A} `{EquDec A} (a : A) (e : omega_regexpr A) : omega_regexpr A :=
  match e with
  | OEzero => OEzero
  | OEsum e_1 e_2 =>
    compute_deriv a e_1 + compute_deriv a e_2
  | OEcat r e =>
    if final r then
      (compute_regular_deriv a r • e) + compute_deriv a e
    else
      (compute_regular_deriv a r) • e
  | OEomega r => compute_regular_deriv a r • OEomega r
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
      exists [],[]. repeat split; auto. now constructor.
    + intros H. simpl in H. destruct H as (w1 & w2 & H1 & H2 & H3).
      simpl. apply andb_true_intro.
      assert (w1 = [] /\ w2 = []) as [H4 H5].
      { inversion H3. destruct w1; try easy. } 
      split. 
      * apply IHe1. now rewrite H4 in H1.
      * apply IHe2. now rewrite H5 in H2.
  - split. 
    + intros H. simpl.
      exists []. split; auto.
      constructor.
    + now intros H.
Qed.

Lemma flatten_help :
  forall {A} `{EQU: Equ A} (l : list (finword A)) (P : finword A -> Prop),
    ~ concat l ≃ [] /\ Forall P l -> exists a w l', Forall P ((a::w)::l') /\ concat l ≃ concat ((a::w)::l').
Proof.
  intros A EQU l P.
  induction l as [|w l IHl].
  - simpl in *. intros [H1 H2]. exfalso. apply H1. constructor.
  - intros [H1 H2]. 
    destruct w.
    + simpl in *.
      destruct IHl as (a & w' & l' & IHl1 & IHl2).
      * split; try easy. now inversion H2.
      * exists a, w', l'. now split.
    + simpl in *. exists a, w, l. now split.
Qed.

Theorem compute_regular_deriv_correct {A} `{EQUDEC: EquDec A} :
  forall (a : A) (e : regexpr A),
    lang_reg (compute_regular_deriv a e) ≃ δ(a, lang_reg e).
Proof.
  intros a e.
  induction e.
  - easy.
  - simpl. easy. 
  - simpl. split.
    + intros w H. unfold regular_deriv_a. unfold regular_deriv_a in *.
      destruct equ_dec.
      * destruct w.
        -- simpl. now constructor. 
        -- easy.
      * destruct w; try easy.
    + intros w H. unfold regular_deriv_a in *.
      destruct equ_dec.
      * destruct w. simpl. constructor. now inversion H.
      * destruct w; try easy.
        simpl. apply n. inversion H; eauto. now inversion H.
  - simpl. split.
    + intros w H. destruct H.
      * left. destruct IHe1 as [H0 H1].
        now apply H0.
      * right. destruct IHe2 as [H0 H1].
        now apply H0.
    + intros w H. destruct H.
      * left. destruct IHe1 as [H0 H1].
        now apply H1.
      * right. destruct IHe2 as [H0 H1].
        now apply H1.
  - Opaque equ. simpl. destruct (final e1) eqn:Feq. 
    + simpl. rewrite IHe2. split.
      * intros w H. destruct H as [(w1 & w2 & H1 & H2 & H3) | ].
        -- exists (a::w1), w2. repeat split; try easy.
           now apply IHe1.
           simpl. now constructor.
        -- exists [], (a::w). repeat split; try easy. 
           now apply empty_exp.
      * intros w H. destruct H as (w1 & w2 & H1 & H2 & H3).
        destruct w1.
        -- right. simpl in H3. now rewrite <- H3 in H2.
        -- left. exists w1, w2. repeat split; auto.
           apply IHe1. unfold regular_deriv_a.
           assert (a0 :: w1 ≃ a :: w1). { constructor. now inversion H3. reflexivity. }
           inversion H3; subst. now rewrite <- H. 
           now inversion H3; subst.
    + simpl. split.
      * intros w H. unfold regular_deriv_a in H|-*.
        destruct H as (w1 & w2 & H1 & H2 & H3).
        exists (a::w1), w2. repeat split; try easy.
        -- destruct IHe1 as [H0 H0']. now apply H0. 
        -- simpl. constructor; try easy. 
      * intros w H. unfold regular_deriv_a in H|-*.
        destruct H as (w1 & w2 & H1 & H2 & H3).
        destruct w1, w2; try easy; simpl in *.
        -- apply empty_exp in H1. now rewrite H1 in Feq.
        -- exists w1, [].
           repeat split; auto.
           ++ apply IHe1. unfold regular_deriv_a. 
              rewrite <- app_nil_end in H3.
              assert (a0::w1 ≃ a::w1). { constructor. now inversion H3. reflexivity. } 
              now rewrite <- H.
           ++ rewrite <- app_nil_end in H3. rewrite <- app_nil_end. now inversion H3; subst. 
        -- exists w1, (a1::w2).
           repeat split; auto. 
           ++ apply IHe1. unfold regular_deriv_a.
              assert( a::w1 ≃ a0::w1). { constructor. now inversion H3. reflexivity. }
              now rewrite H.
           ++ now inversion H3.
  - simpl. split.
    + intros w H. unfold regular_deriv_a.
      destruct H as [w1 [w2 (H1 & [l [H2 H3]] & H4)]].
      exists ((a::w1)::l). split.
      * apply IHe in H1. unfold regular_deriv_a in H1.
        now apply Forall_cons.
      * simpl. constructor; try easy. 
        assert (w1 ++ concat l ≃ w1 ++ w2). { clear H1 H4. induction w1; try easy. constructor; try easy. } 
        etransitivity. now exact H4. now symmetry. 
    + intros w H. unfold regular_deriv_a in H.
      destruct H as (l & H1 & H2).
      destruct (flatten_help l (lang_reg e)) as (b & wb & l' & [H3 H4]).
      split; auto. 
      intros Hf. now assert (a::w ≃ []) by now (transitivity (concat l)). 
      exists wb, (concat l').
      split.
      * apply IHe. unfold regular_deriv_a.
        rewrite <- H2 in H4. clear H2.
        simpl in H4. inversion H4; subst. inversion H3; subst.
        assert (b :: wb ≃ a::wb). { constructor; try easy. }
        now rewrite <- H.
      * split.
      -- exists l'. split; auto. now inversion H3. reflexivity.
      -- rewrite <- H2 in H4. clear H2.
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
    + intros w H. 
      unfold deriv_a.
      inversion H.
      * apply lang_omega_co_sum_l. 
        now apply IHe1.
      * apply lang_omega_co_sum_r.
        now apply IHe2.
    + intros w H. 
      inversion H.
      * apply lang_omega_co_sum_l.
        now apply IHe1.
      * apply lang_omega_co_sum_r.
        now apply IHe2.
  - simpl. destruct (final r) eqn:Feq.
    + split.
      * intros w H. unfold deriv_a.
        apply empty_exp in Feq.
        inversion H.
        -- inversion H3.
           apply compute_regular_deriv_correct in H6. unfold regular_deriv_a in H6.
           now eapply lang_omega_co_cat; eauto.
        -- apply IHe in H3. unfold deriv_a in H3.
           now eapply lang_omega_co_cat; eauto. 
      * intros w H. unfold deriv_a in H.
        inversion H.
        destruct w1.
        -- eapply lang_omega_co_sum_r.
           apply IHe. unfold deriv_a.
           now rewrite H5. 
        -- inversion H5.
           eapply lang_omega_co_sum_l. eapply lang_omega_co_cat.
           apply compute_regular_deriv_correct. unfold regular_deriv_a. exact H2.
           exact H3. easy.
    + split.
      * intros w H. unfold deriv_a.
        inversion H.
        apply compute_regular_deriv_correct in H2. unfold regular_deriv_a in H2.
        now eapply lang_omega_co_cat; eauto.
      * intros w H. unfold deriv_a in H.
        inversion H.
        assert (w1 <> []) as W1.
        { intros W. rewrite W in H2. apply empty_exp in H2. now rewrite H2 in Feq. } 
        destruct w1; try easy.
        eapply lang_omega_co_cat.
        apply compute_regular_deriv_correct. unfold regular_deriv_a.
        assert (a = a0) by now inversion H5.
        rewrite <- H6 in H2; eauto. exact H3. now inversion H5.
  - simpl. split.
    + intros w H. unfold deriv_a in *. 
      inversion H.
      apply compute_regular_deriv_correct in H2. unfold regular_deriv_a in H2.
      eapply lang_omega_co_omega; eauto; easy.
    + intros w H. unfold deriv_a in *.
      inversion H.
      destruct w1; try easy. inversion H4.
      eapply lang_omega_co_cat; eauto. 
      * apply compute_regular_deriv_correct. unfold regular_deriv_a. exact H2.
      * now inversion H4.
Qed.

Theorem deriv_expr_eq {A : Type} `{EquDec A} :
  forall (e1 e2 : omega_regexpr A), 
    lang_omega_co e1 ≃ lang_omega_co e2 <-> forall a, lang_omega_co (compute_deriv a e1) ≃ lang_omega_co (compute_deriv a e2).
Proof.
  intros e1 e2. split.
  - intros H1 a. rewrite compute_deriv_correct. rewrite compute_deriv_correct.
    now rewrite H1. 
  - intros H1. split.
    + intros w H2. destruct w. 
      specialize (H1 x). rewrite (compute_deriv_correct x e1) in H1. 
      rewrite (compute_deriv_correct x e2) in H1.
      now apply H1.
    + intros w H2. destruct w.
      specialize (H1 x). rewrite (compute_deriv_correct x e1) in H1. 
      rewrite (compute_deriv_correct x e2) in H1.
      now apply H1.
Qed. 

(** ** Algorithm *)

Definition ListEquations A := list (omega_regexpr A * omega_regexpr A).

Fixpoint list_in {A} `{Equ A}  (e: A) (l : list A) : Prop := 
  match l with 
  | [] => False 
  | x::l => equ e x \/ list_in e l 
  end.

Class Finite (A : Type) `{EquDec A} :=
{
  all_elem : list A;
  all_elem_correct: forall a, list_in a all_elem;
}.

(** *** Step of Algorithm *)
Definition algo_step {A} `{EquDec A} `{Finite A} (l : ListEquations A) : ListEquations A :=
  match l with 
  | [] => []
  | (e1, e2)::l' =>
    if equ_dec e1 e2 then l' else
    let d := map (fun a => (compute_deriv a e1, compute_deriv a e2)) all_elem in
    l' ++ d
  end.

(** *** Steps of Algorithm *)
CoFixpoint run_algo {A} `{EquDec A} `{Finite A} (l : ListEquations A) : coword (ListEquations A) :=
  lcons l (run_algo (algo_step l)).

Fixpoint get {A} (i : nat) (w : coword A) : A :=
  match w with
  | lcons x w' => match i with 
    | 0 => x 
    | (S i) => get i w'
    end
  end.

(** ** Soundness *)
Definition ValidList {A} `{Equ A} (E : ListEquations A) :=
  forall e1 e2, list_in (e1, e2) E -> lang_omega_co e1 ≃ lang_omega_co e2.

Definition equivList {A} `{Equ A} (E E' : ListEquations A) :=
  ValidList E <-> ValidList E'.

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

#[global]
Instance compute_regular_deriv_morphism_equ {A} `{EquDec A} : Proper (equ ==> equ ==> equ) (@compute_regular_deriv A _).
Proof.
  intros a b H1 e1 e2 H2.
  induction H2; try easy.
  - simpl. destruct (equ_dec a a0) eqn: Hea, (equ_dec b b0) eqn: Heb; try easy.
    + exfalso. apply n. now rewrite <- H1, <- H0.
    + exfalso. apply n. now rewrite H1, H0.
  - simpl. econstructor.
    + now rewrite IHregexpr_equ_ind1.
    + now rewrite IHregexpr_equ_ind2.
  - simpl. destruct (final e1) eqn: Hf1, (final e3) eqn: Hf3.
    + repeat constructor; try easy. 
    + apply empty_exp in Hf1.
      assert (Hf2 : ~final e3 = true) by now rewrite Hf3.
      exfalso. apply Hf2. apply empty_exp.
      eapply equ_morphism_lang; eauto. now symmetry.
    + apply empty_exp in Hf3.
      assert (Hf2 : ~final e1 = true) by now rewrite Hf1.
      exfalso. apply Hf2, empty_exp. 
      now eapply equ_morphism_lang; eauto.
    + constructor; try easy.
  - simpl. constructor; try easy. now constructor.
Defined.

#[global]
Instance compute_deriv_morphism_equ {A} `{EquDec A} : Proper (equ ==> equ ==> equ) (@compute_deriv A _).
Proof.
  intros a b H1 e1 e2 H2.
  induction H2.
  - easy.
  - simpl. now econstructor.
  - simpl. destruct (final e1) eqn: Hf1, (final e2) eqn: Hf2. 
    + repeat econstructor; try easy.
      now rewrite H0, H1.
    + apply empty_exp in Hf1.
      assert (Hf3 : ~final e2 = true) by now rewrite Hf2.
      exfalso. apply Hf3, empty_exp.
      eapply equ_morphism_lang; eauto. now symmetry.
    + apply empty_exp in Hf2.
      assert (Hf3 : ~final e1 = true) by now rewrite Hf1.
      exfalso. apply Hf3, empty_exp.
      eapply equ_morphism_lang; eauto.
    + repeat econstructor; try easy.
      now rewrite H0, H1.
  - simpl. repeat econstructor; try easy.
    now rewrite H0, H1.
Defined.

(** Soundness of Step *)
Theorem algo_step_sound:
  forall {A} `{HF : Finite A} (l1 l2 : ListEquations A),
    algo_step l1 = l2 -> equivList l1 l2.
Proof.
  intros A HD HF l1 l2 H. split. 
  - intros H1.
    rewrite <- H.
    unfold ValidList in *.
    destruct l1.
    + easy.
    + destruct p as [e1 e2].
      unfold algo_step. destruct (equ_dec e1 e2). 
      * intros e3 e4 H2. apply H1.
        simpl. now right.
      * intros e3 e4. intros H2.
        apply in_app_or_equ in H2. destruct H2 as [H2|H2].
        -- apply H1. now right.
        -- apply in_map_iff_equ in H2. destruct H2 as [a [H2 H2']].
           destruct H2 as [<- <-].
           rewrite (compute_deriv_correct a e1). rewrite compute_deriv_correct. 
           pose proof (@deriv_eq A) as [DQ1 DQ2]. 
           apply DQ1. 
              apply H1. now left. 
           intros x y Hxy. split; now rewrite Hxy.
  - destruct l1; try easy. destruct p as [e3 e4].
    intros H1.
    unfold ValidList in *.
    intros e1 e2 H2. 
    unfold algo_step in H. destruct (equ_dec e3 e4).
    + destruct H2 as [H2|H2].
      * simpl in H2. destruct H2 as [-> ->]. now rewrite e.
      * apply H1. now rewrite <- H.
    + destruct H2 as [H2|H2].
      * apply deriv_eq. intros a.
        rewrite <- compute_deriv_correct. rewrite <- compute_deriv_correct. 
        apply H1. rewrite <- H.
        apply in_or_app_equ. right.
        apply in_map_iff_equ.
        intros x y Hxy. split; now rewrite Hxy. 
        exists a. split.
        -- destruct H2 as [H2 H3].
           split; [ now rewrite H2 | now rewrite H3 ].
        -- apply all_elem_correct.
      * apply H1. rewrite <- H.
        apply in_or_app_equ. now left. 
Qed.

(** Soundness of Steps *)
Theorem run_algo_sound:
  forall {A} `{HF : Finite A} (l1 l2 : ListEquations A) i,
    get i (run_algo l1) = l2 -> equivList l1 l2.
Proof.
  intros A HD HF l1 l2 i. 
  induction i in l1 |-*.
  - simpl. intros H. now rewrite H.
  - intros H. simpl in H.
    pose proof (algo_step_sound) as H2.
    specialize (IHi _ H).
    specialize (H2 l1 _ eq_refl).
    unfold equivList in *.
    now rewrite H2.
Qed.

(** Soundness of Equivalence Checker *)
Theorem algo_correct :
  forall {A} `{Finite A} (e1 e2 : omega_regexpr A) i,
    get i (run_algo ([(e1, e2)])) = [] -> lang_omega_co e1 ≃ lang_omega_co e2. 
Proof.
  intros A Equ Fin e1 e2 i H.
  apply run_algo_sound in H as [H1 H2].
  apply H2; try easy. now left.
Qed.


