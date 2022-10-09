Section Integers.
  Inductive Int : Set :=
  | zero : Int
  | succ : Int -> Int
  | opp : Int -> Int.
  
  Declare Scope Int_scope.
  Bind Scope Int_scope with Int.
  Open Scope Int_scope.
  Notation "- n" := (opp n) : Int_scope.
  
  Axiom opp_zero : opp zero = zero.

  Axiom opp_opp : forall n, - - n = n.
  
  Lemma equiv_implies_equiv_succ : 
    forall (n m : Int), n=m -> (succ n) = (succ m).
  Proof.
    intros.
    apply f_equal with (f:= fun t => succ t) in H.
    apply H.
  Qed.
  
  Lemma equiv_succ_implies_equiv : 
    forall (n m : Int), (succ n) = (succ m) -> n = m.
  Proof.
    intros. inversion H. reflexivity.
  Qed.
  
  Fixpoint add (n m : Int) : Int :=
  match n with
  | zero => m
  | succ n' => succ (add n' m)
  | opp n' => - (add n' (- m))
  end.
  
  Infix "+" := add (at level 50, left associativity) : Int_scope.
  Notation "n - m" := (add n (opp m)) : Int_scope.
  
  Lemma add_zero_l : forall (n : Int), zero + n = n.
  Proof.
    trivial.
  Qed.

  Lemma add_zero_r : forall (n : Int), n + zero = n.
  Proof.
    intros. induction n; simpl.
    - reflexivity.
    - rewrite IHn. reflexivity.
    - rewrite opp_zero. rewrite IHn. reflexivity.
  Qed.
  
  Lemma opp_distr : forall (n m : Int), opp (n + m) = (opp n) + (opp m).
  Proof.
    intros. induction n; simpl; repeat rewrite opp_opp; try reflexivity.
  Qed.
  
  Lemma add_succ_l : forall n m, succ n + m = succ (n + m).
  Proof.
    intros. simpl. reflexivity.
  Qed.

  Lemma add_succ_r : forall n m, n + succ m = succ (n + m).
  Proof.
    intros. induction m; simpl.
    - rewrite add_zero_r.
  Qed.

  Theorem add_associativity : 
    forall (i j k : Int), i + (j + k) = (i + j) + k.
  Proof.
    intros. induction k; simpl.
    - repeat rewrite add_zero_r. reflexivity.
    - simpl.  
    
  
  Theorem add_associativity : 
    forall (i j k : Int), i + (j + k) = (i + j) + k.
  Proof.
    intros. induction i.
    simpl. reflexivity.
    simpl. rewrite <- IHi. reflexivity.
    simpl. rewrite <- IHi. reflexivity.
    induction j. induction k.
    all: repeat rewrite add_zero; simpl; try reflexivity.
    repeat rewrite opp_distr, opp_opp. replace (succ (j + k)) with (succ j + k).
    apply f_equal with (f := fun t => i + i + t).
  Qed.
  
  Lemma add_succ_zero : forall (n : Int), succ n = n + succ zero.
  Proof.
    intro. induction n. trivial.
    symmetry. apply f_equal with (f := fun t => succ t) in IHn as IH2. 
    simpl. rewrite <- IH2. reflexivity.
    apply f_equal with (f := fun t => pred t) in IHn as IH2.
    simpl. rewrite <- IH2. rewrite pred_succ_equiv. apply succ_pred_equiv.
    rewrite <- opp_pred. rewrite <- opp_opp. rewrite opp_distr. rewrite opp_opp.
    apply f_equal with (f := fun t => opp t). rewrite opp_succ. rewrite opp_zero.
    replace (pred n) with (pred (n + zero)).
    apply f_equal with (f := fun t => opp t) in IHn as IH2.
    rewrite opp_distr, opp_succ, opp_succ, opp_zero in IH2.
    replace (n + pred zero) with (n + n -n + pred zero).
    rewrite <- IH2.
    
    
  
  Lemma add_succ : forall (n m : Int), succ (n + m) = n + (succ m).
  Proof.
    intros. induction n.
    simpl. reflexivity.
    simpl. rewrite <- IHn. reflexivity.
    simpl. rewrite <- IHn. 
    rewrite succ_pred_equiv. rewrite pred_succ_equiv. reflexivity.
    induction n. induction m. repeat rewrite add_zero in IHn.
    all: 
    
  Theorem add_commutativity : forall (n m : Int), n + m = m + n.
  Proof.
    intros.
    induction n.
    simpl. symmetry. apply add_zero.
    simpl. rewrite IHn. apply add_succ.
    simpl. rewrite IHn. apply add_pred.
  Qed.
  
  Theorem add_closure : forall (n m : Int), exists (x : Int), n + m = x.
  Proof.
    intros. now exists (n + m).
  Qed.
    
  Qed.
  
  Lemma add_pred : forall (n m : Int), pred (n + m) = n + (pred m).
  Proof.
    intros. induction n.
    simpl. reflexivity.
    simpl. rewrite <- IHn. 
    rewrite succ_pred_equiv. rewrite pred_succ_equiv. reflexivity.
    simpl. rewrite <- IHn. reflexivity.
  Qed.
  
  
  Lemma equiv_implies_add_equiv :
    forall (i j k : Int), i = j -> (i + k) = (j + k).
  Proof.
    intros. apply f_equal with (f := fun t => t + k). apply H.
  Qed.
  
  Lemma add_equiv_implies_equiv : 
    forall (i j k : Int), (i + k) = (j + k) -> i = j.
  Proof.
    intros. induction k.
    rewrite add_zero in H. apply H.
    repeat rewrite <- add_succ in H. apply equiv_succ_implies_equiv in H.
    apply IHk. apply H.
    apply IHk. rewrite <- add_pred in H. 
    symmetry. rewrite <- add_pred in H.
    apply f_equal with (f := fun t => succ t) in H.
    rewrite succ_pred_equiv in H. 
    symmetry. rewrite succ_pred_equiv in H.
    apply H.
  Qed.
  
  Lemma add_permutes : forall (i j k : Int), i + j + k = j + k + i.
  Proof.
    intros.
    rewrite <- add_commutativity. rewrite add_associativity.
    symmetry. rewrite <- add_associativity. rewrite add_commutativity.
    reflexivity.
  Qed.
  
  Fixpoint subtract (n m : Int) : Int :=
  match n, m with
  | _, zero => n
  | _, succ m' => pred (subtract n m')
  | _, pred m' => succ (subtract n m')
  end.
  
  Infix "-" := subtract (at level 50, left associativity).
  
  Theorem subtract_anticommutativity : forall (n m : Int), n - m = (zero - m) + n.
  Proof.
    intros. induction m. simpl. reflexivity.
    simpl. symmetry. rewrite <- IHm. reflexivity.
    simpl. symmetry. rewrite <- IHm. reflexivity.
  Qed.
  
  Theorem add_negative : forall (n m : Int), n + (zero - m) = n - m.
  Proof.
    intros. induction m. simpl. apply add_zero.
    simpl. rewrite <- IHm. rewrite add_pred. reflexivity.
    simpl. rewrite <- IHm. rewrite add_succ. reflexivity.
  Qed.
  
  Theorem subtract_add : forall (i j k : Int), i - (j + k) = (i - j) - k.
  Proof.
    intros. induction k. simpl. rewrite add_zero. reflexivity.
    simpl. rewrite <- add_succ. simpl.
    apply f_equal with (f := fun t => pred t). apply IHk.
    simpl. rewrite <- add_pred. simpl.
    apply f_equal with (f := fun t => succ t). apply IHk.
  Qed.
  
  Theorem add_subtract : forall (i j k : Int), i + (j - k) = (i + j) - k.
  Proof.
    intros. induction i. simpl. reflexivity.
    simpl. rewrite IHi. apply f_equal with (f := fun t => pred t). 
    
  
  Fixpoint sign (n : Int) : Int :=
  match n with
  | zero => zero
  | pred zero => pred zero
  |
  
  Fixpoint multiply (n m : Int) : Int :=
  match n with
  | zero => zero
  | succ n' => (multiply n' m) + m 
  | pred n' => (multiply n' m) - m 
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
  
  
    