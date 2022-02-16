Section Group.
  (*First, the very underlying set, identity, group operation, and inverse*)
  Variable G : Set.
  Variable f : G -> G -> G.
  Variable e : G.
  Variable inv : G -> G.
  Infix "<+>" := f (at level 50, left associativity).

  (*Next, the standard group axioms for the right*)
  Variable associativity : forall a b c, (a<+>b)<+>c = a<+>(b<+>c).
  Variable identity_r : forall a, a<+>e = a.
  Variable inverse_r : forall a, a<+>inv a = e.

  Theorem multiply_l (a : G) : forall b c, b = c -> a <+> b = a <+> c.
  Proof.
    intros.
    apply f_equal with (f := fun t => a <+> t) in H.
    apply H.
  Qed. 
  
  Theorem multiply_r (a : G) : forall b c : G, b = c -> b <+> a = c <+> a.
  Proof.
    intros.
    apply f_equal with (f := fun t => t <+> a) in H.
    apply H.
  Qed. 

  Theorem sandwich_identity : forall a b, a<+>e<+>b = a<+>b.
  Proof.
    intros.
    rewrite -> identity_r.
    reflexivity.
  Qed.

  Theorem all_idempotents_are_identity : forall a, a<+>a = a -> a=e.
  Proof.
    intros.
    apply f_equal with (f := fun t => t <+> inv a) in H.
    rewrite -> associativity in H.
    rewrite -> inverse_r in H.
    rewrite identity_r in H.
    apply H.
  Qed.

  Theorem inverse_l : forall a, inv a <+> a = e.
  Proof.
    intros.
    assert ((inv a <+> a) <+> (inv a <+> a) = inv a <+> a).
    {
      rewrite associativity.
      replace (a <+> (inv a <+> a)) with ((a <+> inv a) <+> a).
      rewrite inverse_r.
      rewrite <- associativity.
      rewrite identity_r.
      reflexivity.
      rewrite associativity.
      reflexivity.
    }
    apply all_idempotents_are_identity in H.
    apply H.
  Qed.

  Theorem identity_l : forall a, e<+>a = a.
  Proof.
    intros.
    assert (a <+> inv a <+> a = a).
    {
      rewrite associativity.
      rewrite inverse_l.
      apply identity_r.
    }
    rewrite inverse_r in H.
    apply H.
  Qed.

  Theorem inverse_inverse : forall a, inv (inv a) = a.
  Proof.
    intros.
    assert (a <+> inv a <+> inv (inv a) = a).
    {
      rewrite associativity.
      rewrite inverse_r.
      apply identity_r.
    }
    rewrite inverse_r in H.
    rewrite identity_l in H.
    apply H.
  Qed.

  Theorem inverse_of_product : forall a b, inv (a<+>b) = inv(b)<+>inv(a).
  Proof.
    intros.
    assert (a <+> (b <+> inv (a <+> b)) = a <+> b <+> inv (a <+> b)). 
    rewrite associativity. reflexivity.
    apply f_equal with (f := fun t => inv a <+> t) in H.
    replace (inv a <+> (a <+> (b <+> inv (a <+> b)))) with (b <+> inv (a <+> b)) in H.
    apply f_equal with (f := fun t => inv b <+> t) in H.
    rewrite <- associativity in H.
    rewrite inverse_l in H.
    rewrite identity_l in H.
    rewrite inverse_r in H.
    rewrite identity_r in H.
    apply H.
    rewrite <- associativity.
    rewrite inverse_l.
    rewrite identity_l.
    reflexivity.
  Qed.

  Definition commutes (b : G) := forall a, b <+> a = a <+> b.
  Definition commutes2 (a b : G) := b <+> a = a <+> b.
  Definition abelian := forall a, commutes(a).
  
  Theorem identity_commutes : commutes(e).
  Proof.
    unfold commutes.
    intros.
    rewrite identity_l.
    rewrite identity_r.
    reflexivity.
  Qed.
  
  Definition commutator (a b : G): G := 
    inv a <+> inv b <+> a <+> b.

  Theorem identity_commutator_implies_commutes (a b : G) : 
  commutator(a)(b) = e -> commutes2(a)(b).
    Proof.
      intros.
      unfold commutator in H.
      apply f_equal with (f := fun t => b <+> a <+> t) in H.
      replace (b <+> a <+> (inv a <+> inv b <+> a <+> b)) with (b <+> inv b <+> a <+> b) in H.
      rewrite inverse_r, identity_l, identity_r in H.
      unfold commutes2.
      symmetry. apply H.
      rewrite associativity, associativity.
      rewrite <- sandwich_identity.
      rewrite <- inverse_l with b.
      rewrite <- associativity, <- associativity, <- associativity.
      rewrite inverse_r, identity_l, inverse_r, identity_l.
      rewrite <- associativity, <- associativity, <- associativity.
      replace (b <+> a <+> inv a) with (b).
      rewrite inverse_r, identity_l.
      reflexivity.
      rewrite associativity, inverse_r, identity_r. reflexivity.
      Qed.

End Group.