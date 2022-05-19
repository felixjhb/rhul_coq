Section Interval.
    Inductive I :=
    | zero : I
    | one : I.

    Axiom path : zero = one.

    Theorem function_extensionality : 
        forall (X Y : Type) (f g : X -> Y),  (forall (x : X), f x = g x) -> f = g.
    Proof.
        intros.
        set (q := 
            fun (i : I) => fun (x : X) =>
            match i with
            | zero => f x
            | one => g x
            end).
        assert (q zero = q one) by (rewrite path; reflexivity).
        unfold q in H. simpl in H.
        repeat change (fun x => ?h x) with h in H.
        assumption.
    Qed.
Section End.