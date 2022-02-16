Section SumOfNaturals.
    Inductive nat : Set :=
    | zero : nat
    | succ : nat -> nat.

    Fixpoint add (n m : nat) : nat :=
    match n with
    | zero => m
    | succ n' => succ (add n' m)
    end.

    Infix "+" := add (at level 50, left associativity).
    Notation "0" := zero.
    Notation "1" := (succ zero).
    Notation "2" := (succ 1).
    
    Lemma add_zero_l : forall (n : nat), zero + n = n.
    Proof.
        intros. simpl. reflexivity.
    Qed.
    
    Lemma add_zero_r : forall (n : nat), n + zero = n.
    Proof.
        intros. induction n.
        simpl. reflexivity.
        simpl. rewrite IHn. reflexivity.
    Qed.
    
    Lemma add_succ_l : forall (n m : nat), (succ n) + m = succ (n + m).
    Proof.
        intros. simpl. reflexivity.
    Qed.

    Lemma add_succ_r : forall (n m : nat), n + (succ m) = succ (n + m).
    Proof.
        intros. induction n.
        simpl. reflexivity.
        simpl. rewrite <- IHn. reflexivity.
    Qed.
            
    Theorem add_commutativity : forall (n m : nat), n + m = m + n.
    Proof.
        intros.
        induction n.
        simpl. symmetry. apply add_zero_r.
        simpl. rewrite IHn. rewrite add_succ_r. reflexivity.
    Qed.
            
    Theorem add_associativity : forall (i j k : nat), i + (j + k) = (i + j) + k.
    Proof.
        intros. induction i.
        simpl. reflexivity.
        simpl. rewrite <- IHi. reflexivity.
    Qed.

    Definition pred (n : nat) : nat :=
    match n with
    | zero => zero
    | succ n' => n'
    end.

    Theorem add_normalise_l : forall (i j k : nat), i = j <-> k + i = k + j.
    Proof.
        split.
        intro. apply f_equal with (f := fun t => k + t) in H. apply H.
        intro. induction k.
        simpl in H. apply H.
        simpl in H.
        apply f_equal with (f := fun t => pred t) in H.
        simpl in H. apply (IHk H).
    Qed.

    Theorem add_normalise_r : forall (i j k : nat), i = j <-> i + k = j + k.
    Proof.
        split.
        intro. apply f_equal with (f := fun t => t + k) in H. apply H.
        intro. induction k.
        repeat rewrite add_zero_r in H. apply H.
        repeat rewrite add_succ_r in H.
        apply f_equal with (f := fun t => pred t) in H.
        simpl in H. apply (IHk H).
    Qed.

    Fixpoint multiply (n m : nat) : nat :=
    match n with
    | zero => zero
    | succ n' => m + multiply n' m
    end.

    Infix "*" := multiply (at level 40, left associativity).
  
    Lemma multiply_zero_l : forall (n : nat), zero * n = zero.
    Proof.
        intros. simpl. reflexivity.
    Qed.

    Lemma multiply_zero_r : forall (n : nat), n * zero = zero.
    Proof.
        intros. induction n.
        simpl. reflexivity.
        simpl. apply IHn.
    Qed.

    Lemma multiply_succ_l : forall (n m : nat), (succ n) * m = n * m + m.
    Proof.
        intros. simpl. rewrite add_commutativity. reflexivity.
    Qed.

    Lemma multiply_succ_r : forall (n m : nat), n * (succ m) = n + n * m.
    Proof.
        intros. induction n.
        simpl. reflexivity.
        simpl. rewrite IHn. apply f_equal with (f := fun t => succ t).
        repeat rewrite add_associativity. apply add_normalise_r.
        apply add_commutativity.
    Qed.
    
    Lemma multiply_sum_l : forall (i j k : nat), (i + j) * k = i*k + j*k.
    Proof.
        intros. induction k.
        repeat rewrite multiply_zero_r. simpl. reflexivity.
        rewrite multiply_succ_r. rewrite IHk.
        repeat rewrite multiply_succ_r.
        rewrite <- (add_associativity i (i * k) (j + j * k)).
        rewrite <- (add_associativity i j (i * k + j * k)).
        apply add_normalise_l.
        rewrite add_associativity. rewrite (add_commutativity j (i * k)).
        rewrite <- add_associativity. reflexivity.
    Qed.

    Lemma multiply_sum_r : forall (i j k : nat), i * (j + k) = i*j + i*k.
    Proof.
        intros. induction i.
        simpl. reflexivity.
        simpl. rewrite IHi. repeat rewrite add_associativity.
        apply add_normalise_r.
        rewrite <- (add_associativity j k (i * j)).
        rewrite <- (add_associativity j (i * j) k).
        apply add_normalise_l.
        apply add_commutativity.
    Qed.
  
    Theorem multiply_commutativity : forall (n m : nat), n * m = m * n.
    Proof.
        intros. induction n. 
        rewrite multiply_zero_l, multiply_zero_r. reflexivity.
        rewrite multiply_succ_l, multiply_succ_r,
            add_commutativity, IHn. reflexivity. 
    Qed. 
  
    Theorem multiply_associativity : forall (i j k : nat), i * (j * k) = (i * j) * k.
    Proof.
        intros. induction i. simpl. reflexivity.
        simpl. symmetry. rewrite multiply_commutativity.
        rewrite multiply_sum_r. rewrite multiply_commutativity.
        rewrite add_commutativity.
        rewrite (add_commutativity (j * k) (i * (j * k))).
        apply add_normalise_r. rewrite IHi.
        apply multiply_commutativity.
    Qed.

    (*Sum of the first N natural numbers, multiplied by coefficient k*)
    Fixpoint sum (n k : nat) : nat := 
    match n with
    | zero => zero
    | succ n' => k * succ n' + sum n' k
    end.

    Theorem sum_linear_fnct : forall (n k : nat), sum n k = k * sum n 1.
    Proof.
        intros. induction n.
        simpl. rewrite multiply_zero_r. reflexivity.
        simpl. rewrite IHn, <- (add_associativity n 0 (sum n 1)).
        rewrite <- add_succ_l, add_zero_l.
        rewrite multiply_sum_r. reflexivity.
    Qed.

    Theorem sum_simpl : forall (n : nat), 2 * sum n 1 = n * (succ n).
    Proof.
        intros. rewrite <- sum_linear_fnct.
        induction n.
        simpl. reflexivity.
        simpl. rewrite IHn, add_zero_r.
        rewrite add_succ_r, add_succ_l, (multiply_succ_r _ (succ n)).
        rewrite add_associativity. reflexivity.
    Qed.

    (* Extra exercises borrowed from the book*)

    Inductive bin_nat : Set :=
    | BZ : bin_nat
    | B0 : bin_nat -> bin_nat
    | B1 : bin_nat -> bin_nat.

    Fixpoint bin_succ (n : bin_nat) : bin_nat :=
    match n with
    | BZ => B1 BZ
    | B0 n' => B1 n'
    | B1 n' => B0 (bin_succ n')
    end.

    Fixpoint bin_add (n m : bin_nat) : bin_nat :=
    match n, m with
    | BZ, _ => m
    | _, BZ => n
    | B0 n', B0 m' => B0 (bin_add n' m')
    | B1 n', B0 m' => B1 (bin_add n' m')
    | B0 n', B1 m' => B1 (bin_add n' m')
    | B1 n', B1 m' => B0 (bin_succ (bin_add n' m'))
    end.

    Fixpoint bin_to_nat (n : bin_nat) : nat :=
    match n with
    | BZ => 0
    | B0 n' => 2 * (bin_to_nat n')
    | B1 n' => 1 + 2 * (bin_to_nat n')
    end.

    Theorem bin_equiv_nat_bin_succ : 
        forall (n : bin_nat), succ (bin_to_nat n) = bin_to_nat (bin_succ n).
    Proof.
        intros. induction n; simpl; try reflexivity.
        - repeat rewrite add_zero_r.
          repeat rewrite <- IHn.
          rewrite add_succ_r, add_succ_l.
          reflexivity.
    Qed.

    Fixpoint nat_to_bin (n : nat) : bin_nat :=
    match n with
    | zero => BZ
    | succ n' => bin_succ (nat_to_bin n')
    end.

    (* BZ is like an infinite string of zeroes *)
    Axiom bin_another_zero : B0 BZ = BZ.

    Lemma ntb_double : forall (n : nat),
        nat_to_bin (n + n) = B0 (nat_to_bin n).
    Proof.
        intros. induction n.
        - simpl. rewrite bin_another_zero. reflexivity.
        - rewrite add_succ_r. simpl.
          rewrite IHn. simpl. reflexivity. 
    Qed.

    Theorem identity_btn_ntb : forall (n : bin_nat),
        nat_to_bin (bin_to_nat n) = n.
    Proof.
        intros. induction n; simpl.
        - reflexivity.
        - rewrite add_zero_r, ntb_double, IHn. reflexivity.
        - rewrite add_zero_r, ntb_double, IHn. simpl. reflexivity.  
    Qed.

    Theorem identity_ntb_btn : forall (n : nat),
        bin_to_nat (nat_to_bin n) = n.
    Proof.
        intros. induction n; simpl.
        - reflexivity.
        - rewrite <- bin_equiv_nat_bin_succ, IHn. reflexivity.
    Qed.

End SumOfNaturals.