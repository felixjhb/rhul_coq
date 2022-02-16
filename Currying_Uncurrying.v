Parameters A B C : Set.

Definition curry (f: A * B -> C) := fun a => fun b => f (a, b).
Definition uncurry (f: A -> B -> C) := fun a => f (fst a) (snd a).

Theorem curry_uncurry_ext_eqv : forall f a b, uncurry (curry f) (a, b) = f (a, b).
Proof.
  intros.
  unfold uncurry, curry.
  simpl.
  reflexivity.
Qed.

Theorem uncurry_curry_ext_eqv : forall f a b, curry (uncurry f) (a) (b) = f (a) (b).
Proof.
  intros.
  unfold uncurry, curry.
  simpl.
  reflexivity.
Qed.