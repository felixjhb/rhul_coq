Section NaturalNumbers.
  Inductive Nat : Set :=
  | zero : Nat
  | succ : Nat -> Nat.
  
  Lemma equiv_implies_equiv_succ : 
    forall (n m : Nat), n=m -> (succ n) = (succ m).
  Proof.
    intros.
    apply f_equal with (f:= fun t => succ t) in H.
    apply H.
  Qed.
  
  Definition pred (n : Nat) : Nat :=
  match n with
  | zero => zero
  | succ m => m
  end.
  
  Lemma equiv_succ_implies_equiv : 
    forall (n m : Nat), (succ n) = (succ m) -> n = m.
  Proof.
    intros. induction n.
    destruct m.
    all: apply f_equal with (f := fun t => pred t) in H; simpl in H; apply H.
  Qed.
  
  Fixpoint add (n m : Nat) : Nat :=
  match n, m with
  | zero, _ => m
  | succ n', _ => succ (add n' m)
  end.
  
  Infix "+" := add (at level 50, left associativity).
  
  Lemma add_zero : forall (n : Nat), n + zero = n.
  Proof.
    intros. induction n.
    simpl. reflexivity.
    simpl. rewrite IHn. reflexivity.
  Qed.
  
  Lemma add_succ : forall (n m : Nat), succ (n + m) = n + (succ m).
  Proof.
    intros. induction n.
    simpl. reflexivity.
    simpl. rewrite <- IHn. reflexivity.
  Qed.
  
  Theorem add_commutativity : forall (n m : Nat), n + m = m + n.
  Proof.
    intros.
    induction n.
    simpl. symmetry. apply add_zero.
    simpl. rewrite IHn. apply add_succ.
  Qed.
  
  Theorem add_associativity : 
    forall (i j k : Nat), i + (j + k) = (i + j) + k.
  Proof.
    intros. induction i.
    simpl. reflexivity.
    simpl. rewrite <- IHi. reflexivity.
  Qed.
  
  Theorem add_closure : forall (n m : Nat), exists (x : Nat), n + m = x.
  Proof.
    intros. now exists (n + m).
  Qed.
  
  Lemma equiv_implies_add_equiv :
    forall (i j k : Nat), i = j -> (i + k) = (j + k).
  Proof.
    intros. apply f_equal with (f := fun t => t + k). apply H.
  Qed.
  
  Lemma add_equiv_implies_equiv : 
    forall (i j k : Nat), (i + k) = (j + k) -> i = j.
  Proof.
    intros. induction k.
    repeat rewrite add_zero in H. apply H.
    repeat rewrite <- add_succ in H. apply equiv_succ_implies_equiv in H.
    apply IHk. apply H.
  Qed.
  
  Lemma add_permutes : forall (i j k : Nat), i + j + k = j + k + i.
  Proof.
    intros.
    rewrite <- add_commutativity. rewrite add_associativity.
    symmetry. rewrite <- add_associativity. rewrite add_commutativity.
    reflexivity.
  Qed.
  
  Fixpoint multiply (n m : Nat) : Nat :=
  match n with
  | zero => zero
  | succ n' => m + multiply n' m
  end.
  
  Infix "*" := multiply (at level 40, left associativity).
  
  Lemma multiply_zero : forall (n : Nat), n * zero = zero.
  Proof.
    intros. induction n.
    simpl. reflexivity.
    simpl. apply IHn.
  Qed.
  
  Lemma multiply_succ : forall (n m : Nat), n * (succ m) = n + n * m.
  Proof.
    intros. induction n.
    simpl. reflexivity.
    simpl. rewrite IHn. apply equiv_implies_equiv_succ.
    repeat rewrite add_associativity. apply equiv_implies_add_equiv.
    apply add_commutativity.
  Qed.
  
  Lemma add_multiply : forall (i j k : Nat), i * (j + k) = i*j + i*k.
  Proof.
    intros. induction i.
    simpl. reflexivity.
    simpl. rewrite IHi. repeat rewrite add_associativity.
    apply equiv_implies_add_equiv. rewrite add_permutes.
    symmetry. rewrite add_permutes. apply equiv_implies_add_equiv.
    rewrite add_commutativity. reflexivity.
  Qed.
  
  Theorem multiply_commutativity : forall (n m : Nat), n * m = m * n.
  Proof.
    intros. induction n. 
    rewrite multiply_zero. simpl. reflexivity.
    rewrite multiply_succ. simpl.
    rewrite add_commutativity. symmetry. rewrite add_commutativity.
    apply equiv_implies_add_equiv. symmetry. apply IHn.
  Qed. 
  
  Theorem multiply_associativity :
    forall (i j k : Nat), i * (j * k) = (i * j) * k.
  Proof.
    intros. induction i. simpl. reflexivity.
    simpl. symmetry. rewrite multiply_commutativity.
    rewrite add_multiply. rewrite multiply_commutativity.
    rewrite add_commutativity. symmetry. rewrite add_commutativity.
    apply equiv_implies_add_equiv. rewrite IHi.
    symmetry. apply multiply_commutativity.
  Qed.
  
  Theorem multiply_closure : forall (n m : Nat), exists x, x = n * m.
  Proof.
    intros. now exists (n * m).
  Qed.
  
  Lemma multiply_permutes : forall (i j k : Nat), i * j * k = j * k * i.
  Proof.
    intros. symmetry. rewrite multiply_commutativity.
    apply multiply_associativity.
  Qed.
    