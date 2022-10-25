Set Implicit Arguments.
Unset Strict Implicit.

Definition function_surjective (X Y : Type) (f : X -> Y) : Prop := 
  forall y : Y, exists x : X, f x = y.

Theorem Cantor X : ~ exists f : X -> X -> Prop, function_surjective f.

Proof.
  intros [f A].
  pose (g := fun x => ~ f x x).
  destruct (A g) as [x B].
  assert (C : g x <-> f x x).
  {
    rewrite B. firstorder.
  }
  unfold g in C.
  firstorder.
Qed.