Declare Scope ops.
Delimit Scope ops with ops.

Class InOp (x X : Type) :=
  in_op_ : x -> X -> Prop.

Notation "x ∈ X" := (in_op_ x X) (at level 39) : ops.

Class CupOp (A : Type) :=
  cup_op_ : A -> A -> A.

Notation "x ∪ y" := (cup_op_ x y) (at level 40) : ops.

Class CapOp (A : Type) :=
  cap_op_ : A -> A -> A.

Notation "x ∩ y" := (cap_op_ x y) (at level 40) : ops.

Class SubsetOp (A : Type) :=
  subset_op_ : A -> A -> Prop.

Notation "x ⊂ y" := (subset_op_ x y) (at level 39).

Class SubseteqOp (A : Type) :=
  subseteq_op_ : A -> A -> Prop.

Notation "x ⊆ y" := (subseteq_op_ x y) (at level 39).

Class StepOp (A B : Type) :=
  step_op_ : A -> B -> B -> Prop.

Notation "x $ y --> z" := (step_op_ x y z) (at level 39) : ops.

Class StepsOp (A B : Type) :=
  steps_op_ : A -> B -> B -> Prop.

Notation "x $ y ->* z" := (steps_op_ x y z) (at level 39) : ops.

Class LstepOp (A B C : Type) :=
  lstep_op_ : A -> B -> C -> B -> Prop.

Notation "w $ x -[ y ]-> z" := (lstep_op_ w x y z) (at level 39) : ops.

Class LstepsOp (A B C : Type) :=
  lsteps_op_ : A -> B -> C -> B -> Prop.

Notation "w $ x -[ y ]->* z" := (lsteps_op_ w x y z) (at level 39) : ops.

Class NthOp (A B : Type) :=
  nth_op_ : A -> nat -> B.

Notation "x ⟨ i ⟩" := (nth_op_ x i) (at level 40) : ops.

Class ShiftOp (A B : Type) :=
  shift_op_ : A -> nat -> A.

Notation "x '⟨' i '+⟩'" := (shift_op_ x i) (at level 40) : ops.

Class RangeOp (A B C : Type) :=
  range_op_ : A -> nat -> nat -> C.

Notation "x '⟨' i … j '⟩'" := (range_op_ x i j) (at level 40) : ops.

Reserved Notation "x ⋅ y" (at level 50, left associativity).
Reserved Notation "x • y" (at level 50, left associativity).

Class DotOp1 (A : Type) :=
  dot_op1_ : A -> A -> A.
Notation "x ⋅ y" := (dot_op1_ x y) (at level 50, left associativity) : ops.

Class DotOp2 (A B : Type) :=
  dot_op2_ : A -> B -> B.
Notation "x • y" := (dot_op2_ x y) : ops.

Class AddOp (A : Type) :=
  add_op_ : A -> A -> A.
Notation "x + y" := (add_op_ x y) : ops.

Open Scope ops.