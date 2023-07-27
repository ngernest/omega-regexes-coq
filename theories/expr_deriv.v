From Coq Require Import String List Lia.
From Coq Require Import Classes.Morphisms.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Program.
From equivChecker Require Import utils operators pset syntax words semantics derivatives.
Import ListNotations.

(** * Simplifications Operators for Computing Normalized Derivatives *)

Definition mk_dot_reg {A} `{Equ A} (r1 : regexpr A) (r2 : regexpr A) : regexpr A := 
  match r1, r2 with 
  | Ezero, _ => Ezero
  | _, Ezero => Ezero
  | Eone, r2 => r2 
  | r1, Eone => r1
  | r1, r2 => Ecat r1 r2
  end.
Infix "⊙" := mk_dot_reg (at level 80).

Definition mk_plus_reg {A} `{EquDec A} (r1 r2 : regexpr A) : regexpr A :=
  match r1, r2 with
  | Ezero, r =>  r
  | r, Ezero => r
  | r1, r2 =>
    if equ_dec r1 r2 then r1 else r1 + r2
  end.
Infix "⊕" := mk_plus_reg (at level 80).

Definition mk_dot {A} `{Equ A} (r : regexpr A) (e : omega_regexpr A) : omega_regexpr A :=
  match r, e with 
  | Eone, e => e 
  | Ezero, e => OEzero 
  | r, OEzero => OEzero
  | r, e => OEcat r e 
end.

Definition mk_plus {A} `{EquDec A} (e1 : omega_regexpr A) (e2 : omega_regexpr A) : omega_regexpr A := 
 match e1, e2 with 
 | OEzero, e2 => e2 
 | e1, OEzero => e1 
 | e1, e2 => if equ_dec e1 e2 then e1 else OEsum e1 e2
 end.

(** ** Correctness *)

Lemma simpl_dot_reg_correct {A} `{EQU : Equ A} (e1 : regexpr A) (e2 : regexpr A) :
  lang_reg (mk_dot_reg e1 e2) ≃ lang_reg (Ecat e1 e2).
Proof.
  split.
  - intros w H. unfold In in *. destruct e1, e2; try easy.
    + simpl in H. simpl. 
      exists [], []. repeat split. constructor. constructor. simpl. 
      simpl in H. now inversion H.
    + simpl in H. simpl. exists [], [a].
      repeat split; try repeat constructor.
      reflexivity. easy.
    + simpl in H. destruct H.
      * simpl. exists [], w. now repeat split; try constructor.
      * simpl. exists [], w. now repeat split; try constructor.
    + simpl in H. destruct H as (w1 & w2 & H1 & H2 & H3).
      simpl. exists [], w. repeat split; try constructor.
      exists w1, w2. now repeat split. easy.
    + simpl in H. destruct H as (l & H1 & H2).
      simpl. exists [], w. repeat split; try constructor.
      exists l. now split. easy.
    + simpl in H. simpl. 
      exists [a], []. repeat split; try repeat constructor. 
      reflexivity. easy.
    + simpl in H. destruct H.
      * simpl. exists w, []. repeat split; try constructor; try easy. now rewrite <- app_nil_end.
      * simpl. exists w, []. repeat split. now right. constructor. now rewrite <- app_nil_end.
    +simpl in H. destruct H as (w1 & w2 & H1 & H2 & H3).
      simpl. exists w, []. repeat split.
      exists w1, w2. now repeat split. constructor. now rewrite <- app_nil_end.
    + simpl in H. destruct H as (l & H1 & H2).
      simpl. exists w, []. repeat split.
      exists l. now split. constructor. now rewrite <- app_nil_end.
  - intros w H. unfold In in *. destruct e1, e2; try easy.
    + simpl in *. now repeat destruct H.
    + simpl in *. now repeat destruct H.
    + simpl in *. now repeat destruct H.
    + simpl in *. now repeat destruct H.
    + simpl in *. now repeat destruct H.
    + simpl in *. now repeat destruct H.
    + simpl in *. now repeat destruct H.
    + simpl in *. destruct H as (w1 & w2 & H1 & H2 & H3).
      inversion H1; subst. inversion H2; subst. easy.
    + simpl in *. destruct H as (w1 & w2 & H1 & H2 & H3).
      inversion H1; subst. now transitivity w2.
    + simpl in *. destruct H as (w1 & w2 & H1 & [H2|H2] & H3).
      * inversion H1; subst. left. now rewrite H3.
      * inversion H1; subst. right. now rewrite H3.
    + simpl in *. destruct H as (w1 & w2 & H1 & (w3 & w4 & H2 & H3 & H4) & H5).
      exists w3, w4. repeat split; try easy. 
      rewrite H5, <- H4. destruct w1; try easy.
    + simpl in *. destruct H as (w1 & w2 & H1 & (l & H2 & H3) & H4).
      exists l. split; try easy. 
      rewrite H4, <- H3. now destruct w1.
    + simpl in *. now repeat destruct H.
    + simpl in *. destruct H as (w1 & w2 & H1 & H2 & H3).
      inversion H2; subst. rewrite <- app_nil_end in H3. now transitivity w1.
    + simpl in *. now repeat destruct H.
    + simpl in *. destruct H as (w1 & w2 & [H1|H1] & H2 & H3).
      * inversion H2; subst. left. rewrite <- app_nil_end in H3. now rewrite H3.
      * inversion H2; subst. right. rewrite <- app_nil_end in H3. now rewrite H3.
    + simpl in *. now repeat destruct H.
    + simpl in *. destruct H as (w1 & w2 & (w3 & w4 & H1 & H2 & H3) & H4 & H5).
      exists w3, w4. inversion H4; subst. repeat split; try easy. 
      rewrite <- app_nil_end in H5. now transitivity w1.
    + simpl in *. now repeat destruct H.
    + simpl in *. destruct H as (w1 & w2 & (l & H1 & H2) & H3 & H4).
      exists l. inversion H3; subst. split; try easy. 
      rewrite <- app_nil_end in H4. now transitivity w1.
Qed.
      
Lemma simpl_plus_reg_correct {A} `{EQU : EquDec A} (e1 : regexpr A) (e2 : regexpr A) :
  lang_reg (mk_plus_reg e1 e2) ≃ lang_reg (Esum e1 e2).
Proof.
  split.
  - intros w H. destruct e1, e2; try easy; try (now right); try (now left).
    + simpl in *. destruct (a =? a0).
      * now left.
      * destruct H. now left. now right.
    + Opaque equ_dec. simpl in *. destruct (Esum e1_1 e1_2 =? Esum e2_1 e2_2).
      * now left.
      * destruct H.
        now left. now right.
    + Opaque equ_dec. simpl in *. destruct (Ecat e1_1 e1_2 =? Ecat e2_1 e2_2).
      * now left.
      * destruct H. now left. now right.
    + Opaque equ_dec. simpl in H. destruct (Estar e1 =? Estar e2).
      * now left.
      * destruct H.
        now left. now right.
  - intros w H. destruct e1, e2; try easy; try (now destruct H).
    + simpl in *. destruct H.
      * destruct (Echar a =? Echar a0). easy. now left.
      * destruct (Echar a =? Echar a0). inversion e; subst. rewrite H. simpl. now constructor.
        now right.
    + simpl in *. destruct (Esum e1_1 e1_2 =? Esum e2_1 e2_2), H; try easy.
      * now rewrite e.
      * now left.
      * now right.
    + simpl in *. destruct (Ecat e1_1 e1_2 =? Ecat e2_1 e2_2), H; try easy.
      * now rewrite e.
      * now left.
      * now right.
    + simpl in *. destruct (Estar e1 =? Estar e2), H; try easy.
      * now rewrite e.
      * now left.
      * now right.
Qed.

#[global]
Instance plus_reg_morphsim_equ {A} `{EquDec A} : Proper (equ ==> equ ==> equ) (@Esum A).
Proof.
  intros e1 e2 H1. induction H1; intros e5 e6 H2; destruct H2; now repeat constructor.
Defined.
#[global]
Instance dot_reg_morphsim_equ {A} `{EquDec A} : Proper (equ ==> equ ==> equ) (@Ecat A).
Proof.
  intros e1 e2 H1. induction H1; intros e5 e6 H2; destruct H2; now repeat constructor.
Defined.
#[global]
Instance star_reg_morphsim_equ {A} `{EquDec A} : Proper (equ ==> equ) (@Estar A).
Proof.
  intros e1 e2 H1. induction H1; now repeat constructor.
Defined.
#[global]
Instance plus_morphsim_equ {A} `{EquDec A} : Proper (equ ==> equ ==> equ) (@OEsum A).
Proof.
  intros e1 e2 H1. induction H1; intros e5 e6 H2; destruct H2; now repeat constructor.
Defined.
#[global]
Instance dot_morphsim_equ {A} `{EquDec A} : Proper (equ ==> equ ==> equ) (@OEcat A).
Proof.
  intros e1 e2 H1. induction H1; intros e5 e6 H2; destruct H2; now repeat constructor.
Defined.
#[global]
Instance omega_morphsim_equ {A} `{EquDec A} : Proper (equ ==> equ) (@OEomega A).
Proof.
  intros e1 e2 H1. induction H1; now repeat constructor.
Defined.

#[global]
Instance mk_plus_reg_morphism_equ {A} `{EquDec A} : Proper (equ ==> equ ==> equ) (@mk_plus_reg A _).
Proof.
  intros e1 e2 H1. induction H1; intros e5 e6 H2; destruct H2; try (now repeat constructor).
  - simpl. destruct (Echar a =? Echar a0), (Echar b =? Echar b0).
    + now constructor.
    + exfalso. apply n. constructor. inversion e; subst. 
      transitivity a; try easy. now transitivity a0.
    + exfalso. apply n. constructor. inversion e; subst. 
      transitivity b; try easy. now transitivity b0.
    + now repeat constructor.
  - simpl. destruct (Esum e1 e2 =? Esum e0 e5), (Esum e3 e4 =? Esum e6 e7); try easy.
    + now constructor.
    + exfalso. apply n. now rewrite <- H2_, <- H2_0, <- e, H1_, H1_0.
    + exfalso. apply n. now rewrite  H2_,  H2_0, <- e, H1_, H1_0.
    + constructor. 
      now rewrite H1_, H1_0.
      now rewrite H2_0, H2_.
  - simpl. destruct (Ecat e1 e2 =? Ecat e0 e5), (Ecat e3 e4 =? Ecat e6 e7); try easy.
    + now constructor.
    + exfalso. apply n. now rewrite <- H2_, <- H2_0, <- e, H1_, H1_0.
    + exfalso. apply n. now rewrite  H2_,  H2_0, <- e, H1_, H1_0.
    + constructor. now rewrite H1_, H1_0. now rewrite H2_, H2_0.
  - simpl. destruct (Estar e1 =? Estar e0), (Estar e2 =? Estar e3); try easy.
    + now constructor.
    + exfalso. apply n. now rewrite <- H1, e, H2.
    + exfalso. apply n. now rewrite H1, e, <- H2.
    + constructor. now rewrite H1. now rewrite H2.
Defined.

#[global]
Instance mk_plus_morphism_equ {A} `{EquDec A} : Proper (equ ==> equ ==> equ) (@mk_plus A _).
Proof.
  intros e1 e2 H1. induction H1; intros e5 e6 H2; destruct H2; try (now repeat constructor).
  - simpl. destruct (e1 + e3 =? e0 + e6), (e2 + e4 =? e5 + e7); try easy.
    + now constructor.
    + exfalso. apply n. now rewrite <- H1_, <- H1_0, e, H2_, H2_0.
    + exfalso. apply n. now rewrite H1_, H1_0, e, H2_, H2_0.
    + constructor. now rewrite H1_, H1_0. now rewrite H2_0, H2_.
  - simpl. destruct (e1 • e3 =? e0 • e6), (e2 • e4 =? e5 • e7); try easy.
    + now constructor.
    + exfalso. apply n. now rewrite <- H0, <- H1, e, H2, H3.
    + exfalso. apply n. now rewrite H0, H1, e, H2, H3.
    + constructor. now rewrite H0, H1. now rewrite H2, H3.
  - simpl. destruct (OEomega e1 =? OEomega e0), (OEomega e2 =? OEomega e3).
    + now constructor.
    + exfalso. apply n. now rewrite <- H0, e, H1.
    + exfalso. apply n. now rewrite H0, e, H1.
    + constructor. now rewrite H0. now rewrite H1.
Defined.

#[global]
Instance mk_dot_reg_morphism_equ {A} `{EquDec A} : Proper (equ ==> equ ==> equ) (@mk_dot_reg A _).
Proof.
  intros e1 e2 H1. induction H1; intros e5 e6 H2; destruct H2; now repeat constructor.
Defined.
#[global]
Instance mk_dot_morphism_equ {A} `{EquDec A} : Proper (equ ==> equ ==> equ) (@mk_dot A _).
Proof.
  intros e1 e2 H1. induction H1; intros e5 e6 H2; destruct H2; now repeat constructor.
Defined.

Lemma simpl_dot_correct {A} `{EQU : Equ A} (e1 : regexpr A) (e2 : omega_regexpr A) :
  lang_omega_co (mk_dot e1 e2) ≃ lang_omega_co (OEcat e1 e2).
Proof.
  split.
  - intros w H. destruct e1, e2; try easy.
    + simpl in *. inversion H; subst.
      * econstructor. simpl. reflexivity. exact H. easy.
      * econstructor. simpl. reflexivity. exact H. easy.
    + simpl in *. econstructor. simpl. reflexivity.
      exact H. easy.
    + simpl in *. 
      econstructor. simpl. reflexivity.
      exact H. easy.
  - intros w H. destruct e1, e2; try easy.
    + simpl in *. inversion H; subst. inversion H2.
    + simpl in *. inversion H; subst. inversion H2.
    + simpl in *. inversion H; subst. inversion H2.
    + simpl in *. inversion H; subst. inversion H2.
    + simpl in *. inversion H; subst. inversion H2. 
      rewrite <- H0 in H5. now rewrite H5.
    + simpl in *. inversion H; subst. inversion H2.
      rewrite <- H0 in H5. now rewrite H5.
    + simpl in *. inversion H; subst. inversion H2.
      rewrite <- H0 in H5. now rewrite H5.
    + simpl in *. inversion H; subst. inversion H2.
      rewrite <- H0 in H5. now rewrite H5.
    + simpl in *. inversion H; subst. destruct w; try easy. 
    + simpl in *. inversion H; subst. destruct w; try easy.
    + simpl in *. inversion H; subst. destruct w; try easy.
    + simpl in *. inversion H; subst. destruct w; try easy.
Qed.
Lemma simpl_plus_correct {A} `{EQU : EquDec A} (e1 : omega_regexpr A) (e2 : omega_regexpr A) :
  lang_omega_co (mk_plus e1 e2) ≃ lang_omega_co (OEsum e1 e2).
Proof.
  split.
  - intros w H. destruct e1, e2; try easy.
    + simpl in *. now econstructor 2. 
    + simpl in *. now econstructor 2.
    + simpl in *. now econstructor 2.
    + simpl in *. now econstructor.
    + simpl in *. destruct (OEsum e1_1 e1_2 =? OEsum e2_1 e2_2).
      * now econstructor.
      * easy.
    + simpl in *. now econstructor.
    + simpl in *. destruct (OEcat r e1 =? OEcat r0 e2).
      * now econstructor.
      * easy.
    + simpl in *. now econstructor.
    + simpl in *. destruct (OEomega r =? OEomega r0).
      now econstructor. easy.
  - intros w H. destruct e1, e2; try easy; try (now inversion H).
    + simpl in *. destruct (OEsum e1_1 e1_2 =? OEsum e2_1 e2_2); try easy.
      inversion H; try easy. now rewrite e.
    + simpl in *. destruct (OEcat r e1 =? OEcat r0 e2); try easy.
      inversion H. easy. now rewrite e.
    + simpl in *. destruct (OEomega r =? OEomega r0); try easy.
      inversion H. easy. now rewrite e.
Qed.

