Create HintDb hdb.

Require Import Ring.
Require Import Morphisms.

Section Integers.
  Inductive PosZ : Set :=
  | pz_one : PosZ
  | pz_succ : PosZ -> PosZ.
  
  Fixpoint PosZadd (n m : PosZ) : PosZ :=
  match n with
  | pz_one => pz_succ m
  | pz_succ n' => pz_succ (PosZadd n' m)
  end.
  
  Fixpoint PosZmultiply (n m : PosZ) : PosZ :=
  match n with
  | pz_one => m
  | pz_succ n' => PosZadd (PosZmultiply n' m) m
  end.
  
  Inductive Nat : Set :=
  | nat_zero : Nat
  | nat_succ : Nat -> Nat.
  
  Fixpoint inject_PZ_Nat (n : PosZ) : Nat :=
  match n with
  | pz_one => nat_succ nat_zero
  | pz_succ n' => nat_succ (inject_PZ_Nat n')
  end.
  
  Coercion inject_PZ_Nat : PosZ >-> Nat.
  
  Lemma PosZ_not_Nat_zero : forall n : PosZ,
    inject_PZ_Nat n <> nat_zero.
  Proof.
    intros n H. induction n; discriminate.
  Qed.
  
  Inductive Int : Set :=
  | zero : Int
  | succ : Int -> Int
  | pred : Int -> Int.
  
  Fixpoint inject_Nat_Int (n : Nat) : Int :=
  match n with
  | nat_zero => zero
  | nat_succ n' => succ (inject_Nat_Int n')
  end.
  
  Coercion inject_Nat_Int : Nat >-> Int.
  
  Lemma PosZ_not_Int_zero : forall n : PosZ,
    inject_Nat_Int (inject_PZ_Nat n) <> nat_zero.
  Proof.
    intros n H. induction n; discriminate.
  Qed.
  
  Declare Scope Int_scope.
  Delimit Scope Int_scope with Int.
  Bind Scope Int_scope with Int.
  Open Scope Int_scope.
  Notation "1" := (pz_one) : Int_scope.
  Notation "0" := (nat_zero) : Int_scope.
  Notation "-1" := (pred zero) : Int_scope.
  
  Axiom pred_succ : forall (n : Int), pred (succ n) = n.
  
  Axiom succ_pred : forall (n : Int), succ (pred n) = n.
  
  Lemma equiv_succ : 
    forall (n m : Int), n = m <-> succ n = succ m.
  Proof.
    split. intro. 
    apply f_equal with (f:= fun t => succ t) in H.
    apply H.
    intro. apply f_equal with (f := fun t => pred t) in H.
    rewrite pred_succ in H. 
    symmetry in H. rewrite pred_succ in H.
    symmetry in H. apply H.
  Qed.
  
  Lemma equiv_pred : 
    forall (n m : Int), n = m <-> pred n = pred m.
  Proof.
    split. intro. 
    apply f_equal with (f:= fun t => pred t) in H.
    apply H.
    intro. apply f_equal with (f := fun t => succ t) in H.
    rewrite succ_pred in H. 
    symmetry in H. rewrite succ_pred in H.
    symmetry in H. apply H.
  Qed.
  
  Fixpoint Zadd (n m : Int) : Int :=
  match n with
  | zero => m
  | succ n' => succ (Zadd n' m)
  | pred n' => pred (Zadd n' m)
  end.
  
  Arguments Zadd _%Int _%Int.
  
  Infix "+" := Zadd (at level 50, left associativity) : Int_scope.
  
  Theorem PosZadd_Zadd_coincide : forall (a b : PosZ),
    inject_Nat_Int (inject_PZ_Nat (PosZadd a b)) = a + b.
  Proof.
    intros. induction a. trivial.
    simpl. rewrite IHa. reflexivity.
  Qed.
  
  Lemma add_zero_r : forall (n : Int), n + zero = n.
  Proof.
    intros. induction n.
    simpl. reflexivity.
    simpl. rewrite IHn. reflexivity.
    simpl. apply f_equal with (f := fun t => pred t). apply IHn.
  Qed.
  Hint Resolve add_zero_r : hdb.
  
  Lemma add_zero_l : forall (n : Int), zero + n = n.
  Proof.
    intros. simpl. reflexivity.
  Qed.
  Hint Resolve add_zero_l : hdb.
  
  Lemma add_zero_m : forall (n m : Int), n + zero + m = n + m.
  Proof.
    intros. rewrite add_zero_r. reflexivity.
  Qed.
  Hint Resolve add_zero_m : hdb.
  
  Lemma add_succ : forall (n m : Int), succ (n + m) = n + (succ m).
  Proof.
    intros. induction n.
    simpl. reflexivity.
    simpl. rewrite <- IHn. reflexivity.
    simpl. rewrite <- IHn. 
    rewrite succ_pred. rewrite pred_succ. reflexivity.
  Qed.
  Hint Resolve add_succ : hdb.
  
  Lemma add_pred : forall (n m : Int), pred (n + m) = n + (pred m).
  Proof.
    intros. induction n.
    simpl. reflexivity.
    simpl. rewrite <- IHn. 
    rewrite succ_pred. rewrite pred_succ. reflexivity.
    simpl. rewrite <- IHn. reflexivity.
  Qed.
  Hint Resolve add_pred : hdb.
  
  Theorem add_assoc : 
    forall (i j k : Int), i + (j + k) = (i + j) + k.
  Proof.
    intros. induction i.
    simpl. reflexivity.
    simpl. rewrite <- IHi. reflexivity.
    simpl. rewrite <- IHi. reflexivity.
  Qed.
  Hint Resolve add_assoc : hdb.
  
  Theorem add_comm : forall (n m : Int), n + m = m + n.
  Proof.
    intros.
    induction n.
    simpl. symmetry. apply add_zero_r.
    simpl. rewrite IHn. apply add_succ.
    simpl. rewrite IHn. apply add_pred.
  Qed.
  Hint Resolve add_comm : hdb.
  
  Lemma add_one : forall (n : Int), succ n = n + 1.
  Proof.
    intro. rewrite add_comm. simpl. reflexivity.
  Qed.
  Hint Resolve add_one : hdb.
  
  Theorem add_closure : forall (n m : Int), exists (x : Int), n + m = x.
  Proof.
    intros. now exists (n + m).
  Qed.
  
  Lemma equiv_add :
    forall (i j k : Int), i = j <-> (i + k) = (j + k).
  Proof.
    split. intro. 
    apply f_equal with (f := fun t => t + k). apply H.
    intro. induction k.
    repeat rewrite add_zero_r in H. apply H.
    repeat rewrite <- add_succ in H. apply equiv_succ in H.
    apply IHk. apply H.
    apply IHk. rewrite <- add_pred in H. 
    symmetry. rewrite <- add_pred in H.
    apply f_equal with (f := fun t => succ t) in H.
    rewrite succ_pred in H. 
    symmetry. rewrite succ_pred in H.
    apply H.
  Qed.
  Hint Resolve equiv_add : hdb.
  
  Lemma add_permute : forall (i j k : Int), i + j + k = j + k + i.
  Proof.
    intros.
    rewrite <- add_comm. rewrite add_assoc.
    symmetry. rewrite <- add_assoc. rewrite add_comm.
    reflexivity.
  Qed.
  Hint Resolve add_permute : hdb.
  
  Fixpoint Zopp (n : Int) : Int :=
  match n with
  | zero => zero
  | succ n' => pred (Zopp n')
  | pred n' => succ (Zopp n')
  end.
  
  Notation "- n" := (Zopp n) : Int_scope.
  
  Lemma opp_succ : forall (n : Int), - (succ n) = pred (- n).
  Proof.
    intros. induction n. all: simpl; reflexivity.
  Qed.
  Hint Resolve opp_succ : hdb.
  
  Lemma opp_pred : forall (n : Int), - (pred n) = succ (- n).
  Proof.
    intros. induction n. all: simpl; reflexivity.
  Qed.
  Hint Resolve opp_pred : hdb.
  
  Notation "n - m" := (Zadd n (- m)) : Int_scope.
  
  Lemma opp_opp : forall (n : Int), - (- n) = n.
  Proof.
    intro. induction n. all: simpl. reflexivity.
    all: rewrite IHn; reflexivity.
  Qed.
  Hint Resolve opp_opp : hdb.
  
  Lemma opp_one : - (1) = -1.
  Proof.
    trivial.
  Qed.
  Hint Resolve opp_one : hdb.
  
  Lemma add_negone : forall (n : Int), pred n = n - 1.
  Proof.
    intro. rewrite add_comm. simpl. reflexivity.
  Qed.
  Hint Resolve add_one : hdb.
  
  Theorem add_inv : forall (n : Int), n - n = zero.
  Proof.
    intros. induction n. simpl; reflexivity.
    simpl. rewrite <- add_pred, IHn. apply succ_pred.
    simpl. rewrite <- add_succ, IHn. apply pred_succ.
  Qed.
  Hint Resolve add_inv : hdb.
  
  Lemma opp_distr : forall (n m : Int), - (n + m) = (- n) + (- m).
  Proof.
    intros. induction m. repeat rewrite add_zero_r. reflexivity. 
    all: simpl. rewrite <- opp_succ.
    induction n. all: simpl. reflexivity.
    
    symmetry; rewrite <- opp_succ. rewrite IHn. reflexivity.
    apply f_equal with (f := fun t => - t) in IHm as IH2.
    rewrite opp_opp in IH2. simpl in IH2.
    apply equiv_succ in IH2.
    rewrite IH2. rewrite opp_opp. reflexivity.
    
    symmetry; rewrite <- opp_succ. rewrite IHn. reflexivity.
    apply f_equal with (f := fun t => - t) in IHm as IH2.
    rewrite opp_opp in IH2. simpl in IH2.
    apply equiv_pred in IH2.
    rewrite IH2. rewrite opp_opp. reflexivity.
    
    rewrite <- add_succ. rewrite <- add_pred. rewrite opp_pred.
    apply -> equiv_succ. apply IHm. 
  Qed.
  Hint Resolve opp_distr : hdb.
  
  Lemma swap_sides_eqn : forall i j k, i = j - k <-> i + k = j.
  Proof.
    split. intro. apply f_equal with (f := fun t => t + k) in H.
    rewrite <- add_assoc in H. rewrite H. rewrite add_comm, <- add_zero_r.
    symmetry. rewrite add_comm. apply equiv_add. rewrite add_comm, add_inv.
    reflexivity.
    intro. apply f_equal with (f := fun t => t - k) in H.
    rewrite <- add_assoc, add_inv, add_zero_r in H. assumption.
  Qed.
  
  Lemma eq_implies_add_inv : forall n m, n = m -> n - m = 0.
  Proof.
    intros. apply f_equal with (f := fun t => t - m) in H.
    rewrite add_inv in H. assumption.
  Qed.
  
  Lemma add_inv_implies_eq : forall n m, n - m = 0 -> n = m.
  Proof.
    intros. apply swap_sides_eqn in H.
    rewrite opp_opp in H. simpl in H.
    assumption.
  Qed.
  
  Inductive lte (n : Int) : Int -> Prop :=
  | lte_id : lte n n
  | lte_s : forall (m : Int), lte n m -> lte n (succ m).
  
  Definition lt (n m : Int) := lte (succ n) m.
  
  Notation gte a b := (lte b a) (only parsing).
  Notation gt a b := (lt b a) (only parsing).
  
  Infix "n <= m" := (lte n m) (at level 70, no associativity) : Int_scope.
  Infix "n < m" := (lt n m) (at level 70, no associativity) : Int_scope.
  Infix "n >= m" := (gte n m) (at level 70, no associativity) : Int_scope.
  Infix "n > m" := (gt n m) (at level 70, no associativity) : Int_scope.
  
  Theorem lte_not_1_0 : (lte 1 0 -> False).
  Proof.
    intro. inversion H.
  Qed.
  
  Lemma lte_invar_lr_add : forall (i j : Int), 
    lte i j <-> (forall (n : Int), lte (i+n) (j+n)).
  Proof.
    split. intros. induction H. apply (lte_id (i + n)).
    rewrite add_one. rewrite <- add_permute. rewrite <- add_one.
    apply lte_s. replace (n + m) with (m + n). assumption.
    apply add_comm.
    
    intros. remember (H 0) as G. clear HeqG. 
    repeat rewrite add_zero_r in G. assumption.
  Qed.
  
  Lemma lte_invar_lr_sub : forall (i j k : Int),
    lte (i+k) (j+k) -> lte i j.
  Proof.
    intros. apply lte_invar_lr_add with (n:= -k) in H.
    repeat rewrite <- add_assoc in H. rewrite add_inv in H.
    repeat rewrite add_zero_r in H. assumption.
  Qed.
  
  Lemma lt_not_id : forall n, lt n n -> False.
  Proof.
    intros. unfold lt in H. rewrite add_one in H. 
    rewrite add_comm in H. replace (lte (1 + n) n) with (lte (1 + n) (0 + n)) in H.
    apply lte_invar_lr_sub in H. apply lte_not_1_0. assumption.
    trivial.
  Qed.
  
  Theorem lte_trans : forall i j k, lte i j -> lte j k -> lte i k.
  Proof.
    intros i j k H G.
    
    induction H. induction G. apply lte_id. apply lte_s. assumption.
    
    apply IHlte. apply lte_s in G. 
    replace (succ k) with (k + 1) in G. rewrite add_one in G.
    apply lte_invar_lr_sub in G. assumption.
    rewrite <- add_one. reflexivity.
  Qed.
  
  Theorem lt_trans : forall i j k, lt i j -> lt j k -> lt i k.
  Proof.
    intros i j k H G. unfold lt. unfold lt in H, G.
    apply lte_s in G. rewrite add_one in G.
    replace (succ k) with (k + 1) in G.
    apply lte_invar_lr_sub in G.
    apply (lte_trans (succ i) j k H G).
    rewrite <- add_one. reflexivity.
  Qed.
  
  Theorem lte_min_or_more : forall i j, lte i j <-> i = j \/ lte (succ i) j.
  Proof.
    split. intro. induction H. left. reflexivity.
    destruct IHlte as [Ieq | Ilt].
    
    right. rewrite Ieq. apply lte_id.
    right. apply lte_s in Ilt. assumption.
    
    intro. destruct H as [Ieq | Ilt]. rewrite Ieq. apply lte_id.
    
    apply lte_s in Ilt.
    rewrite add_one in Ilt. replace (succ j) with (j + 1) in Ilt.
    apply lte_invar_lr_sub in Ilt. assumption.
    
    rewrite <- add_one. reflexivity.
  Qed.
  
  Theorem lte_max_or_less : forall i j, lte i j <-> i = j \/ lte i (pred j).
  Proof.
    split. intro. induction H. left. reflexivity.
    destruct IHlte as [Ieq | Ilt].
    
    right. rewrite Ieq, pred_succ. apply lte_id.
    right. apply lte_s in Ilt. rewrite succ_pred in Ilt.
    rewrite pred_succ. assumption.
    
    intro. destruct H as [Ieq | Ilt]. rewrite Ieq. apply lte_id.
    
    apply lte_s in Ilt.
    rewrite succ_pred in Ilt. assumption.
  Qed.
  
  Theorem lt_not_eq : forall i j, lt i j -> i <> j.
  Proof.
    intros. intro. induction i. induction j. unfold lt in H.
    
    apply lte_not_1_0. assumption.
    all: rewrite H0 in H; apply lt_not_id in H; assumption.
  Qed.
  
  Theorem lte_definite : forall i j, lte i j -> lte j i -> i = j.
  Proof.
    intros i j lte_ij lte_ji.
    
    apply lte_min_or_more in lte_ij. apply lte_min_or_more in lte_ji.
    destruct lte_ij as [eqij | ltij]. destruct lte_ji as [eqji | ltji].
    
    assumption. assumption.
    destruct lte_ji as [eqji | ltji].
    
    symmetry in eqji. assumption.
    set (H := lt_trans i j i ltij ltji).
    apply lt_not_id in H. contradiction.
  Qed.
  
  Lemma lte_opp : forall (a b : Int), lte a b -> lte (- b) (- a).
  Proof.
    intros. induction H. apply (lte_id (- a)). 
    rewrite opp_succ.
    set (G := lte_id (pred (- m))).
    apply lte_s in G. rewrite succ_pred in G.
    apply (lte_trans (pred (-m)) (-m) (-a) G IHlte).
  Qed.
  
  Definition positive (n : Int) := lt zero n.
  Definition negative (n : Int) := lt n zero.
  
  Inductive positive' : Int -> Prop :=
  | pos_one : positive' 1
  | pos_s : forall (m : Int), positive' m -> positive' (m + 1).
  
  Inductive negative' : Int -> Prop :=
  | neg_one : negative' -1
  | neg_p : forall (m : Int), negative' m -> negative' (m - 1).
  
  Definition Sign (n : Int) := n = 0 \/ positive n \/ negative n.
  
  Definition positive_one : positive 1.
  Proof.
    apply (lte_id 1).
  Qed.
  
  Definition negative_one : negative -1.
  Proof.
    unfold negative, lt. rewrite succ_pred. apply (lte_id 0).
  Qed.
  
  Theorem int_sign : forall n, Sign n.
  Proof.
    intro. unfold Sign.
    unfold positive, negative, lt. simpl.
    induction n.
    left. reflexivity.
    
    all: destruct IHn as [Cz | [Cp | Cn]].
    
    right. left. rewrite Cz. apply (lte_id 1).
    right. left. apply lte_s. assumption.
    destruct Cn.
    left. reflexivity.
    right. right.
    rewrite (add_one (succ n)). rewrite (add_one m).
    apply lte_invar_lr_add with (n := 1). assumption.
    
    right. right. rewrite succ_pred, Cz. apply (lte_id 0).
    destruct Cp. 
    left. rewrite pred_succ. reflexivity.
    right. left. rewrite pred_succ. assumption.
    right. right. rewrite succ_pred.
    apply lte_s in Cn.
    rewrite (add_one zero) in Cn. rewrite add_one in Cn.
    apply lte_invar_lr_sub with (k := 1) in Cn.
    assumption.
  Qed.
  
  Ltac destruct_sign n := 
    let Cs := fresh "Csign" in idtac;
    let Cz := fresh "Cz" in idtac;
    let Cp := fresh "Cp" in idtac;
    let Cn := fresh "Cn" in idtac;
    set (Cs := int_sign n);
    destruct Cs as [Cz | [Cp | Cn]];
    try rewrite Cz.
  
  Lemma positive_positive'_coincide : forall (n : Int),
    positive n <-> positive' n.
  Proof.
    split. intro. induction n.
    unfold positive, lt in H.
    apply lte_not_1_0 in H. contradiction.
    
    inversion H. apply pos_one. rewrite add_one. apply pos_s.
    apply IHn. assumption.
    
    induction H. apply pos_one. rewrite add_one. apply pos_s.
    assumption.
    
    intro. induction H. apply (lte_id 1).
    unfold positive. rewrite <- add_one. apply lte_s.
    assumption.
  Qed.
  
  Lemma negative_negative'_coincide : forall (n : Int),
    negative n <-> negative' n.
  Proof.
    split. intro. inversion H.
    intro. induction H.
    
    unfold negative. unfold lt. rewrite succ_pred.
    apply (lte_id 0).
    
    rewrite <- add_negone. unfold negative, lt. rewrite succ_pred.
    unfold negative, lt in IHnegative'.
    set (G := lte_id m). apply lte_s in G.
    apply (lte_trans m (succ m) 0 G IHnegative').
  Qed.
  
  Lemma lte_invar_r_add : forall (i j : Int), 
    lte i j -> forall (n : Int), (n = 0 \/ positive n) -> lte i (j+n).
  Proof.
    intros. destruct H0 as [C0 | CP].
    rewrite C0, add_zero_r. assumption.
    apply positive_positive'_coincide in CP.
    induction CP. rewrite <- add_one. apply lte_s. assumption.
    rewrite add_assoc. rewrite <- add_one. apply lte_s.
    assumption.
  Qed.
  
  Lemma pos_sum : forall (n m : Int), positive n -> positive m -> positive (n + m).
  Proof.
    intros n m H G. 
    apply positive_positive'_coincide in H, G.
    apply positive_positive'_coincide.
    
    induction G. apply pos_s. assumption.
    rewrite add_assoc. apply pos_s. assumption.
  Qed.
  
  Lemma neg_sum : forall (n m : Int), negative n -> negative m -> negative (n + m).
  Proof.
    intros n m H G. 
    apply negative_negative'_coincide in H, G.
    apply negative_negative'_coincide.
    
    induction G. apply neg_p. assumption.
    rewrite add_assoc. apply neg_p. assumption.
  Qed.
  
  Theorem zero_signless : ((positive 0 -> False) /\ (negative 0 -> False))
    /\ ((positive' 0 -> False) /\ (negative' 0 -> False)).
  Proof.
    split.
    split; intro; apply lt_not_eq in H; contradiction.
    split; intro; 
    apply positive_positive'_coincide in H || 
      apply negative_negative'_coincide in H;
    apply lt_not_eq in H; contradiction.
  Qed.
  
  Fixpoint abs (n : Int) :=
  match n with
  | zero => zero
  | succ n' => abs n' + 1
  | pred n' => abs n' + 1
  end.
  
  Lemma abs_pos : forall (n : Int), (n = 0) \/ positive (abs n).
  Proof.
    intros. induction n. left. reflexivity.
    
    all: destruct IHn; right; try rewrite H; simpl; try apply (lte_id 1).
    all: rewrite <- add_one; apply lte_s; assumption.
  Qed.
  
  Lemma abs_opp : forall (n : Int), abs (- n) = abs n.
  Proof.
    intro. induction n. trivial.
    all: rewrite opp_succ || rewrite opp_pred; simpl; rewrite IHn; reflexivity.
  Qed.
  
  Lemma pos_equiv_abs : forall (n : Int), positive n -> abs n = n.
  Proof.
    intros. induction H. simpl. reflexivity.
    simpl. rewrite <- add_one, IHlte. reflexivity.
  Qed.
  
  Lemma neg_equiv_abs : forall (n : Int), negative n -> abs n = - n.
  Proof.
    intros. inversion H.
  Qed.
  
  Lemma abs_pos_neg : forall (n : Int), abs n = n \/ abs n = - n.
  Proof.
    intros. destruct_sign n. left. simpl. reflexivity.
    left. apply (pos_equiv_abs n Cp).
    right. apply (neg_equiv_abs n Cn).
  Qed.
  
  Lemma abs_sum_ineq : forall (i j : Int), lte (abs (i + j)) (abs i + abs j).
  Proof.
    intros.
    
    induction j. simpl. repeat rewrite add_zero_r. apply lte_id. 
    
    all: simpl; rewrite <- add_pred || rewrite <- add_succ; simpl;
    rewrite add_assoc; apply -> lte_invar_lr_add; assumption.
  Qed.
  
  Theorem abs_zero : forall n, abs n = 0 <-> n = 0.
  Proof.
    split. 
    
    intro. set (G := abs_pos n). destruct G as [C0 | CG0].
    assumption.
    rewrite H in CG0. apply (lt_not_id 0) in CG0. contradiction.
    
    intro. rewrite H. trivial.
  Qed.
  
  Theorem triangle_ineq : forall (i j k : Int),
    lte (abs (i - k)) (abs (i - j) + abs (j - k)).
  Proof.
    intros. induction j. simpl. rewrite add_zero_r, abs_opp.
    induction k. simpl. repeat rewrite add_zero_r. apply (lte_id (abs i)).
    
    rewrite opp_succ. rewrite <- add_pred. simpl. rewrite add_assoc.
    apply -> lte_invar_lr_add. assumption.
    
    rewrite opp_pred. rewrite <- add_succ. simpl. rewrite add_assoc.
    apply -> lte_invar_lr_add. assumption.
    
    simpl. rewrite <- add_pred. simpl. 
    rewrite add_assoc, <- add_one, <- add_permute, <- add_one.
    apply lte_s, lte_s.
    replace (abs (j - k) + abs (i - j)) with (abs (i - j) + abs (j - k)).
    assumption. rewrite add_comm. reflexivity.
    
    simpl. rewrite <- add_succ. simpl. 
    rewrite add_assoc, <- add_one, <- add_permute, <- add_one.
    apply lte_s, lte_s.
    replace (abs (j - k) + abs (i - j)) with (abs (i - j) + abs (j - k)).
    assumption. rewrite add_comm. reflexivity.
    
  Qed.
  
  Fixpoint Zmultiply (n m : Int) : Int :=
  match n with
  | zero => zero
  | succ n' => (Zmultiply n' m) + m 
  | pred n' => (Zmultiply n' m) - m 
  end.
  
  Infix "*" := Zmultiply (at level 40, left associativity) : Int_scope.
  
  Theorem PosZmultiply_Zmultiply_coincide : forall (a b : PosZ),
    inject_Nat_Int (inject_PZ_Nat (PosZmultiply a b)) = a * b.
  Proof.
    intros. simpl. induction a.
    trivial.
    simpl. rewrite PosZadd_Zadd_coincide, IHa. reflexivity.
  Qed.
  
  Lemma multiply_zero : forall (n : Int), n * zero = zero.
  Proof.
    intro. induction n.
    simpl. reflexivity.
    all: simpl; rewrite add_zero_r; apply IHn.
  Qed.
  
  Lemma multiply_id_r : forall (n : Int), n * 1 = n.
  Proof.
    intro. simpl. induction n. trivial.
    all: simpl; rewrite IHn;
    rewrite <- add_succ || rewrite <- add_pred;
    rewrite add_zero_r; reflexivity.
  Qed.
  
  Lemma multiply_succ : forall (n m : Int), n * (succ m) = n * m + n.
  Proof.
    intros. induction n.
    simpl. reflexivity.
    simpl. rewrite IHn. rewrite add_permute, <- add_succ.
    symmetry. rewrite add_permute, <- add_succ.
    apply equiv_add. apply -> equiv_succ. apply add_comm.
    
    simpl. rewrite IHn. rewrite add_permute, <- add_pred.
    symmetry. rewrite add_permute, <- add_pred.
    apply equiv_add. apply -> equiv_pred. apply add_comm.
  Qed.
  
  Lemma multiply_pred : forall (n m : Int), n * (pred m) = n * m - n.
  Proof.
    intros. induction n.
    simpl. reflexivity.
    simpl. rewrite IHn. rewrite add_permute, <- add_pred.
    symmetry. rewrite add_permute, <- add_pred.
    apply equiv_add. apply -> equiv_pred. apply add_comm.
    
    simpl. rewrite IHn. rewrite add_permute, <- add_succ.
    symmetry. rewrite add_permute, <- add_succ.
    apply equiv_add. apply -> equiv_succ. apply add_comm.
  Qed.
  
  Lemma multiply_distr : forall (i j k : Int), i * (j + k) = i*j + i*k.
  Proof.
    intros. induction i.
    simpl. reflexivity.
    simpl. rewrite IHi. repeat rewrite add_assoc.
    apply equiv_add. rewrite <- add_permute.
    apply equiv_add. apply add_comm.
    simpl. rewrite opp_distr.
    replace (i * j - j + (i * k - k)) with (i * j + i * k + (- j - k)).
    apply equiv_add. apply IHi.
    rewrite add_permute. symmetry. rewrite add_permute.
    repeat rewrite add_assoc.
    repeat (apply equiv_add || apply add_comm).
  Qed.
  
  Lemma multiply_opp_r : forall (n m : Int), n * (- m) = - (n * m).
  Proof.
    intros. induction m.
    simpl. rewrite multiply_zero. trivial.
    all: simpl; rewrite multiply_succ, multiply_pred, opp_distr, IHm; 
         try rewrite opp_opp; reflexivity.
  Qed.
  
  Lemma multiply_opp_l : forall (n m : Int), (- n) * m = - (n * m).
  Proof.
    intros. induction m.
    simpl. repeat rewrite multiply_zero. trivial.
    rewrite multiply_succ, multiply_succ, opp_distr, IHm. reflexivity.
    rewrite multiply_pred, multiply_pred, opp_distr, IHm. reflexivity.
  Qed.
  
  Lemma multiply_distr_sub : forall i j k, i * (j - k) = i * j - i * k.
  Proof.
    intros. rewrite multiply_distr, multiply_opp_r. reflexivity.
  Qed.
  
  Theorem multiply_comm : forall (n m : Int), n * m = m * n.
  Proof.
    intros. induction m. 
    rewrite multiply_zero. simpl. reflexivity.
    rewrite multiply_succ. simpl. rewrite IHm. reflexivity.
    simpl. replace (pred m) with (pred (m + 0)).
    rewrite add_pred. rewrite multiply_distr. simpl.
    rewrite <- opp_one, multiply_opp_r, multiply_id_r, IHm. reflexivity.
    rewrite add_zero_r. reflexivity.
  Qed. 
  
  Theorem multiply_assoc :
    forall (i j k : Int), i * (j * k) = (i * j) * k.
  Proof.
    intros. induction i. simpl. reflexivity.
    
    simpl. symmetry. rewrite multiply_comm.
    rewrite multiply_distr. rewrite multiply_comm.
    rewrite add_comm. symmetry. rewrite add_comm.
    rewrite IHi. apply equiv_add, multiply_comm.
    
    simpl. symmetry. rewrite multiply_comm, multiply_distr, multiply_opp_r.
    replace (k * j) with (j * k).
    apply equiv_add. rewrite multiply_comm.
    symmetry. apply IHi. apply multiply_comm.
  Qed.
  
  Theorem multiply_closure : forall (n m : Int), exists x, x = n * m.
  Proof.
    intros. now exists (n * m).
  Qed.
  
  Lemma multiply_permute : forall (i j k : Int), i * j * k = j * k * i.
  Proof.
    intros. symmetry. rewrite multiply_comm.
    apply multiply_assoc.
  Qed.
  
  Lemma Int_ring_theory : ring_theory zero (succ zero) Zadd Zmultiply (fun a b => a - b) Zopp eq.
  Proof.
    constructor. all: intros. 
    rewrite add_comm, add_zero_r. reflexivity.
    apply add_comm.
    apply add_assoc.
    rewrite multiply_comm, multiply_id_r. reflexivity.
    apply multiply_comm.
    apply multiply_assoc.
    rewrite multiply_comm, multiply_distr, multiply_comm, add_comm, multiply_comm, add_comm. reflexivity.
    reflexivity.
    apply add_inv.
  Qed.
  
  Add Ring ZRing : Int_ring_theory.
  
  Lemma pos_multiply : forall (n m : Int), positive n -> positive m -> positive (n * m).
  Proof.
    intros n m H G. induction H. simpl. assumption.
    simpl. apply pos_sum. all: assumption.
  Qed.
  
  (*Theorem neg_neg_pos : forall n, negative (- n) -> positive n.
  Proof.
    intros k H.
    
    induction k. simpl in H. 
    apply zero_signless in H; contradiction.
    rewrite add_one. 
    unfold positive, lt. rewrite add_one, add_assoc.
    apply -> lte_invar_lr_add. rewrite add_zero_r.
    
    unfold positive, negative, lt in H, IHk.
    rewrite opp_succ, succ_pred in H. 
    apply lte_invar_lr_add with (n:=k) in H.
    rewrite add_comm, add_inv in H. simpl in H. assumption.
    
    unfold positive, negative, lt in H, IHk.
    rewrite add_negone.
    unfold positive, lt.
    rewrite opp_pred, add_one, add_one in H.
    replace (lte (- k + 1 + 1) 0) with (lte (- k + 1 + 1) (-1 + 1)) in H.
    apply lte_invar_lr_sub in H. rewrite add_comm in H.
    apply lte_invar_lr_add with (n := k) in H.
    replace (1 - k + k) with 1 in H. replace (-1 + k) with (k - 1) in H.
    assumption. rewrite add_comm. reflexivity.
    symmetry. rewrite <- add_zero_r. symmetry. rewrite add_comm, add_permute.
    apply equiv_add. rewrite add_comm, add_inv. reflexivity.
    replace (-1 + 1) with 0. reflexivity.
    rewrite add_comm, add_inv. reflexivity.
  Qed.*)
  
  Theorem neg_neg_pos : forall n, negative (- n) -> positive n.
  Proof.
    intros. unfold negative, lt in H. unfold positive, lt.
    rewrite <- opp_pred in H.
    apply lte_opp in H.
    simpl in H. rewrite opp_opp in H.
    rewrite add_negone in H.
    apply lte_invar_lr_add with (n := 1) in H.
    rewrite opp_one, <- (add_assoc n -1 1), add_inv, add_zero_r in H.
    simpl in H. assumption.
  Qed.
  
  Theorem pos_neg_neg : forall n, positive n -> negative (- n).
  Proof.
    intros. unfold positive, lt in H. unfold negative, lt.
    rewrite <- opp_pred.
    apply (lte_opp zero (pred n)).
    replace (succ zero) with (0 + 1) in H by trivial. 
    replace n with (n - 1 + 1) in H by ring.
    apply (lte_invar_lr_sub) in H.
    replace (n - 1) with (pred n) in H by (rewrite add_negone; reflexivity).
    assumption.
  Qed.
  
  Theorem positive_and_negative : forall (n : Int),
    positive n -> negative n -> False.
  Proof.
    intros n Hp Hn. apply pos_neg_neg in Hp.
    set (Hcon := neg_sum n (- n) Hn Hp).
    rewrite add_inv in Hcon. apply zero_signless in Hcon.
    contradiction.
  Qed.
  
  Theorem lte_add_pos_r : forall n m, positive m -> lt n (n + m).
  Proof.
    intros. induction n. assumption. simpl.
    replace (succ n) with (n + 1) by (rewrite <- add_one; reflexivity).
    replace (succ (n + m)) with (n + m + 1) by (rewrite <- add_one; reflexivity).
    unfold lt. replace (succ (n + 1)) with ((succ n) + 1) by trivial.
    apply lte_invar_lr_add with (n := 1). assumption.
    
    unfold lt. rewrite succ_pred. simpl.
    apply lte_invar_lr_sub with (k := 1).
    replace (n + 1) with (succ n) by (rewrite add_one; reflexivity).
    simpl. rewrite <- (add_succ (n + m)), pred_succ, add_zero_r.
    assumption.
  Qed.
  
  Theorem lte_add_neg_l : forall n m, negative m -> lt (n + m) n.
  Proof.
    intros. induction n. assumption. simpl.
    replace (succ n) with (n + 1) by (rewrite <- add_one; reflexivity).
    replace (succ (n + m)) with (n + m + 1) by (rewrite <- add_one; reflexivity).
    unfold lt. replace (succ (n + m + 1)) with (succ (n + m) + 1) by trivial.
    apply lte_invar_lr_add with (n := 1). assumption.
    
    unfold lt. simpl. rewrite succ_pred.
    apply lte_invar_lr_sub with (k := 1).
    replace (n + m + 1) with (succ (n + m)) by (rewrite add_one; reflexivity).
    replace (pred n + 1) with (n) by
      (rewrite <- add_one, succ_pred; reflexivity).
    assumption.
  Qed.
  
  Theorem abs_pos_sum : forall n m,
    positive n -> positive m -> abs (n + m) = abs n + abs m.
  Proof.
    intros n m H G.
    
    induction G. rewrite <- add_one. trivial.
    inversion H. simpl. symmetry. rewrite add_one. reflexivity.
    
    rewrite H1. rewrite <- add_succ. simpl.
    rewrite add_assoc. rewrite IHG. reflexivity.
  Qed.
  
  Theorem abs_neg_sum : forall n m,
    negative n -> negative m -> abs (n + m) = abs n + abs m.
  Proof.
    intros n m H G. rewrite <- opp_opp in H, G.
    apply neg_neg_pos in H, G.
    rewrite <- abs_opp.
    replace (abs n) with (abs (- n)) by (rewrite abs_opp; trivial).
    replace (abs m) with (abs (- m)) by (rewrite abs_opp; trivial).
    rewrite opp_distr.
    apply abs_pos_sum. all: assumption.
  Qed.
  
  Lemma pos_pos_product : forall (n m : Int),
    positive n -> positive m -> positive (n * m).
  Proof.
    intros n m H G.
    
    induction H. simpl. assumption.
    simpl. apply pos_sum. all: assumption.
  Qed.
  
  Lemma pos_neg_product : forall (n m : Int),
    positive n -> negative m -> negative (n * m).
  Proof.
    intros n m H G.
    
    inversion H. simpl. assumption. 
    inversion G.
  Qed.
  
  Lemma neg_pos_product : forall (n m : Int),
    negative n -> positive m -> negative (n * m).
  Proof.
    intros n m H G.
    rewrite multiply_comm. apply (pos_neg_product m n G H).
  Qed.
  
  Lemma neg_neg_product : forall (n m : Int),
    negative n -> negative m -> positive (n * m).
  Proof.
    intros n m H G. inversion H.
  Qed.
  
  Lemma pos_product_sign : forall (n m : Int),
    positive (n * m) -> 
      (positive n /\ positive m) \/ (negative n /\ negative m).
  Proof.
    intros n m H. destruct_sign n.
    rewrite Cz in H. simpl in H.
    apply zero_signless in H. contradiction.
    
    destruct_sign m.
    rewrite Cz in H. rewrite multiply_zero in H.
    apply zero_signless in H. contradiction.
    
    left. split; assumption.
    
    exfalso.
    set (Hcon := pos_neg_product n m Cp Cn).
    apply (positive_and_negative (n * m) H Hcon).
    
    destruct_sign m.
    rewrite Cz in H. rewrite multiply_zero in H.
    apply zero_signless in H. contradiction.
    
    exfalso.
    set (Hcon := neg_pos_product n m Cn Cp).
    apply (positive_and_negative (n * m) H Hcon).
    
    right. split; assumption.
  Qed.
  
  Lemma pos_product_pos : forall (n m : Int),
    positive n -> positive (n * m) -> positive m.
  Proof.
    intros n m H G. apply pos_product_sign in G.
    destruct G as [[Hnp Hmp] | [Hnn Hnm]].
    assumption.
    exfalso. apply (positive_and_negative n H Hnn).
  Qed.
  
  Lemma lazy_positive_to_lte : forall n, positive n -> lte 0 n.
  Proof.
    intros. unfold positive, lt in H.
    apply lte_s in H.
    rewrite add_one, (add_one n) in H.
    apply lte_invar_lr_sub in H.
    assumption.
  Qed.
  
  Lemma lazy_negative_to_lte : forall n, negative n -> lte n 0.
  Proof.
    intros. rewrite <- opp_opp in H.
    apply neg_neg_pos, lazy_positive_to_lte, lte_opp in H.
    ring_simplify in H. assumption.
  Qed.
  
  Lemma lte_abs : forall (n m : Int),
    positive m -> (lte (abs n) m <-> lte (- m) n /\ lte n m).
  Proof.
    split. intros.
    destruct_sign n.
    
    rewrite Cz in H0. simpl in H0.
    apply lte_opp in H0 as H2. simpl in H2.
    split; assumption.
    
    rewrite -> (pos_equiv_abs n Cp) in H0.
    apply pos_neg_neg in H.
    apply lazy_positive_to_lte in Cp.
    apply lazy_negative_to_lte in H.
    apply (lte_trans (- m) 0 n H) in Cp.
    split; assumption.
    
    rewrite -> (neg_equiv_abs n Cn) in H0.
    apply lte_opp in H0. ring_simplify in H0.
    apply lazy_positive_to_lte in H.
    apply lazy_negative_to_lte in Cn.
    apply (lte_trans n 0 m Cn) in H.
    split;assumption.
    
    intro. destruct H0.
    destruct (abs_pos_neg n).
    
    rewrite H2; assumption.
    rewrite H2. apply lte_opp in H0.
    ring_simplify in H0. assumption.
  Qed.
  
  Lemma abs_product_eq : forall (n m : Int),
    abs (n * m) = abs n * abs m.
  Proof.
    intros.
    
    destruct_sign n.
    simpl. reflexivity.
    all: destruct_sign m.
    
    simpl. repeat rewrite multiply_zero. simpl. reflexivity.
    
    set (H := pos_pos_product n m Cp Cp0).
    rewrite (pos_equiv_abs n Cp).
    rewrite (pos_equiv_abs m Cp0).
    rewrite (pos_equiv_abs (n * m) H).
    reflexivity.
    
    set (H := pos_neg_product n m Cp Cn).
    rewrite (pos_equiv_abs n Cp).
    rewrite (neg_equiv_abs m Cn).
    rewrite (neg_equiv_abs (n * m) H).
    rewrite multiply_opp_r. reflexivity.
    
    simpl. repeat rewrite multiply_zero. simpl. reflexivity.
    
    set (H := pos_neg_product m n Cp Cn). rewrite multiply_comm in H.
    rewrite (neg_equiv_abs n Cn).
    rewrite (pos_equiv_abs m Cp).
    rewrite (neg_equiv_abs (n * m) H).
    simpl. rewrite multiply_opp_l. reflexivity.
    
    set (H := neg_neg_product n m Cn Cn0).
    rewrite (neg_equiv_abs n Cn).
    rewrite (neg_equiv_abs m Cn0).
    rewrite (pos_equiv_abs (n * m) H).
    rewrite multiply_opp_r, multiply_opp_l, opp_opp. reflexivity.
  Qed.
  
  Lemma lte_invar_r_mul : forall (i j : Int),
    (j = 0 \/ positive j) -> lte i j ->
    forall (n : Int), positive n -> lte i (j * n).
  Proof.
    intros. induction H1.
    rewrite multiply_id_r. assumption.
    rewrite multiply_succ. apply lte_invar_r_add.
    all: assumption.
  Qed.
  
  Lemma abs_product_lte : forall (n m : Int),
    m <> 0 -> lte (abs n) (abs (n * m)).
  Proof.
    intros.
    rewrite abs_product_eq.
    set (Gn := abs_pos n). set (Gm := abs_pos m).
    destruct Gm. contradiction.
    
    apply lte_invar_r_mul.
    
    destruct Gn.
    left. apply abs_zero. assumption.
    right. assumption.
    apply (lte_id (abs n)). assumption.
  Qed.
  
  Lemma zero_implies_product_zero : forall (n m : Int), 
    (n = 0) \/ (m = 0) -> n * m = 0.
  Proof.
    intros. destruct H as [H | G]. rewrite H. trivial.
    rewrite G, multiply_zero. reflexivity.
  Qed.
  
  Lemma product_zero_implies_zero : forall (n m : Int),
    n * m = 0 -> (n = 0) \/ (m = 0).
  Proof.
    intros.
    destruct_sign n. left. reflexivity.
    destruct_sign m. right. reflexivity.
    
    set (G := pos_pos_product n m Cp Cp0).
    rewrite H in G. apply zero_signless in G. contradiction.
    
    set (G := pos_neg_product n m Cp Cn).
    rewrite H in G. apply zero_signless in G. contradiction.
    
    destruct_sign m. right. reflexivity.
    
    set (G := neg_pos_product n m Cn Cp).
    rewrite H in G. apply zero_signless in G. contradiction.
    
    set (G := neg_neg_product n m Cn Cn0).
    rewrite H in G. apply zero_signless in G. contradiction.
  Qed.
  
  Lemma pos_neg_one_implies_product_one : forall (n m : Int),
    ((n = 1) /\ (m = 1)) \/ ((n = -1) /\ (m = -1)) -> n * m = 1.
  Proof.
    intros. destruct H; destruct H as [H G]; rewrite H, G; trivial.
  Qed.
  
  Theorem product_one_implies_pos_neg_one : forall (n m : Int),
    n * m = 1 -> ((n = 1) /\ (m = 1)) \/ ((n = -1) /\ (m = -1)).
  Proof.
    intros. apply f_equal with (f := fun t => abs t) in H as Habs.
    simpl in Habs.
    
    assert (m <> 0). intro. rewrite H0 in H.
    rewrite multiply_zero in H. discriminate.
    
    set (G := abs_product_lte n m H0).
    rewrite H in G. simpl in G.
    apply (lte_abs n 1 (lte_id 1)) in G. destruct G as [n_min n_max].
    
    assert (n <> 0).
    intro. rewrite H1 in H. simpl in H1. discriminate.
    
    set (G := abs_product_lte m n H1).
    rewrite multiply_comm, H in G. simpl in G.
    apply (lte_abs m 1 (lte_id 1)) in G. destruct G as [m_min m_max].
    
    apply lte_max_or_less in m_max.
    destruct m_max as [Cm1 | m_max].
    rewrite Cm1 in H. rewrite multiply_id_r in H.
    left. split; assumption.
    
    apply lte_min_or_more in m_min.
    destruct m_min as [Cmn1 | m_min].
    rewrite <- Cmn1 in H. rewrite multiply_opp_r, multiply_id_r in H.
    apply f_equal with (f := fun t => - t) in H. 
    rewrite opp_opp in H. simpl in H, Cmn1. symmetry in Cmn1. 
    right. split; assumption.
    
    simpl in m_min. rewrite succ_pred in m_min.
    simpl in m_max. rewrite pred_succ in m_max.
    
    set (Hcon := lte_definite m 0 m_max m_min).
    rewrite Hcon, multiply_zero in H. discriminate.
  Qed.
  
  Lemma eq_implies_multiply_eq_l : forall (i j k : Int),
    (i = j -> k * i = k * j).
  Proof.
    intros. rewrite H. reflexivity.
  Qed.
  
  Lemma eq_implies_multiply_eq_r : forall (i j k : Int),
    (i = j -> i * k = j * k).
  Proof.
    intros. rewrite H. reflexivity.
  Qed.
  
  Lemma eq_multiply_implies_eq_l : forall (i j k : Int), 
    k <> 0 -> k * i = k * j -> i = j.
  Proof.
    intros i j k Hkz H.
    generalize (eq_implies_add_inv _ _ H).
    intro. rewrite <- multiply_distr_sub in H0.
    destruct (product_zero_implies_zero _ _ H0).
    contradiction.
    apply add_inv_implies_eq in H1. assumption.
  Qed.
  
  Lemma eq_multiply_implies_eq_r : forall (i j k : Int), 
    k <> 0 -> i * k = j * k -> i = j.
  Proof.
    intros.
    rewrite (multiply_comm i k) in H0.
    rewrite (multiply_comm j k) in H0.
    apply (eq_multiply_implies_eq_l _ _ _ H H0).
  Qed.
  
  Inductive mod : Int -> Int -> Int -> Prop  := (*mod n a r ⇔ a ≡ r mod n*)
  | mod_id : forall (n : Int), mod n 0 0
  | mod_zero : forall (a : Int), mod 0 a a
  | mod_cycle : forall (n a r m : Int), (mod n a r) -> (mod n a (r + m*n)).
  
  Notation "a ≡ r mod n" := (mod n a r) (at level 90, no associativity): Int_scope.
  
  
  Fixpoint iterate_fn {T : Type} (f : T -> T) (n : Nat) (t : T) : T :=
  match n with
  | nat_zero => t
  | nat_succ n' => f (iterate_fn f n' t)
  end.
  
  Set Printing Coercions.

  Inductive Int' : Set :=
  | z0 : Int'
  | zpos : PosZ -> Int'
  | zneg : PosZ -> Int'.
  
  Definition Z'succ (n : Int') : Int' :=
  match n with
  | z0 => zpos pz_one
  | zpos n' => zpos (pz_succ n')
  | zneg n' => match n' with
               | pz_one => z0
               | pz_succ m => zneg m 
               end
  end.
  
  Definition Z'pred (n : Int') : Int' :=
  match n with
  | z0 => zneg pz_one
  | zpos n' => match n' with
               | pz_one => z0
               | pz_succ m => zpos m 
               end
  | zneg n' => zneg (pz_succ n')
  end.
  
  Definition Z'opp (n : Int') : Int' :=
  match n with
  | z0 => z0
  | zpos n' => zneg n'
  | zneg n' => zpos n'
  end.
  
  Definition inject_Int'_Int (n : Int') :=
  match n with
  | z0 => zero
  | zpos m => iterate_fn succ m zero
  | zneg m => iterate_fn pred m zero
  end.
  
  Fixpoint inject_Int_Int' (n : Int) :=
  match n with
  | zero => z0
  | succ n' => Z'succ (inject_Int_Int' n')
  | pred n' => Z'pred (inject_Int_Int' n')
  end.
  
  Theorem surjection_Int_Int' : forall (n : Int'), exists (m : Int),
    n = inject_Int_Int' m.
  Proof.
    intro. unfold inject_Int_Int'. induction n.
    exists zero. reflexivity.
    exists p. induction p. trivial.
    simpl. rewrite <- IHp. trivial.
    exists (- p). induction p. trivial.
    simpl. rewrite <- IHp. trivial.
  Qed.
  
  Lemma Z'succ_zpos : forall n : PosZ,
    Z'succ (zpos n) = zpos (pz_succ n).
  Proof.
    auto.
  Qed.
  
  Lemma Z'pred_zneg : forall n : PosZ,
    Z'pred (zneg n) = zneg (pz_succ n). (*n - 1 = - *)
  Proof.
    auto.
  Qed.
  
  Lemma Z_Z'_succ : forall (n : Int) (m : Int'),
    n = inject_Int'_Int m -> m = inject_Int_Int' n ->
    succ n = inject_Int'_Int (Z'succ m).
  Proof.
    intros. induction m; simpl.
    rewrite H. trivial.
    simpl in H. rewrite H. reflexivity.
    rewrite H.
    induction p;
    simpl; rewrite succ_pred; reflexivity.
  Qed.
  
  Lemma Z'_Z_succ : forall (n : Int) (m : Int'),
    n = inject_Int'_Int m -> m = inject_Int_Int' n ->
    inject_Int_Int' (succ n) = Z'succ m.
  Proof.
    intros. induction m; simpl;
    rewrite <- H0; reflexivity.
  Qed.
  
  Lemma Z_Z'_pred : forall (n : Int) (m : Int'),
    n = inject_Int'_Int m -> m = inject_Int_Int' n ->
    pred n = inject_Int'_Int (Z'pred m).
  Proof.
    intros. induction m; simpl.
    rewrite H. trivial.
    induction p; rewrite H; 
    simpl; rewrite pred_succ; reflexivity.
    simpl in H. rewrite <- H. reflexivity.
  Qed.
  
  Lemma Z'_Z_pred : forall (n : Int) (m : Int'),
    n = inject_Int'_Int m -> m = inject_Int_Int' n ->
    inject_Int_Int' (pred n) = Z'pred m.
  Proof.
    intros. induction m; simpl;
    rewrite <- H0; reflexivity.
  Qed.
  
  Theorem surjection_Z'_Z : forall (n : Int), exists (m : Int'),
    n = inject_Int'_Int m.
  Proof.
    intro. induction n.
    exists z0. trivial.
    
    destruct IHn. exists (Z'succ x).
    unfold Z'succ. rewrite H.
    induction x; try trivial.
    unfold inject_Int'_Int, iterate_fn.
    destruct p; simpl; rewrite succ_pred; reflexivity.
    
    destruct IHn. exists (Z'pred x).
    unfold Z'pred. rewrite H.
    induction x; try trivial.
    unfold inject_Int'_Int, iterate_fn.
    destruct p; simpl; rewrite pred_succ; reflexivity.
  Qed.
  
  Theorem coercion_Z'_Z_Z'_id : forall (n : Int'),
    n = inject_Int_Int' (inject_Int'_Int n).
  Proof.
    intros. induction n. trivial.
    
    induction p. trivial.
    simpl. rewrite <- Z'succ_zpos.
    apply f_equal with (f := fun t => Z'succ t).
    rewrite IHp. trivial.
    
    induction p. trivial.
    simpl. rewrite <- Z'pred_zneg.
    apply f_equal with (f := fun t => Z'pred t).
    rewrite IHp. trivial.
  Qed.
  
  Theorem coercion_Z_Z'_Z_id : forall (n : Int),
    n = inject_Int'_Int (inject_Int_Int' n).
  Proof.
    intros. induction n;
    simpl; try (apply Z_Z'_succ || apply Z_Z'_pred); trivial.
  Qed.
  
  
  Theorem Int_Int'_coercion_equiv : forall n m,
    inject_Int_Int' n = m <-> inject_Int'_Int m = n.
  Proof.
    split; intro;
    induction H; symmetry;
    apply coercion_Z'_Z_Z'_id || apply coercion_Z_Z'_Z_id.
  Qed.
  
  Coercion inject_Int'_Int : Int' >-> Int.
  Coercion inject_Int_Int' : Int >-> Int'.
  
  Lemma Z_Z'_eq_succ : forall (n : Int) (m : Int'),
    n = m -> succ n = Z'succ m /\ succ m = Z'succ n.
  Proof.
    intros. split. rewrite Z_Z'_succ with (m := n).
    rewrite H. rewrite <- coercion_Z'_Z_Z'_id. trivial.
    rewrite <- coercion_Z_Z'_Z_id. trivial.
    trivial.
    
    rewrite Z_Z'_succ with (m := n).
    rewrite H. rewrite <- coercion_Z'_Z_Z'_id. trivial.
    symmetry. rewrite <- coercion_Z_Z'_Z_id. trivial.
    rewrite <- coercion_Z'_Z_Z'_id.
    apply Int_Int'_coercion_equiv. symmetry. trivial.
  Qed.
  
  Lemma Z_Z'_eq_pred : forall (n : Int) (m : Int'),
    n = m -> pred n = Z'pred m /\ pred m = Z'pred n.
  Proof.
    intros. split. rewrite Z_Z'_pred with (m := n).
    rewrite H. rewrite <- coercion_Z'_Z_Z'_id. trivial.
    rewrite <- coercion_Z_Z'_Z_id. trivial.
    trivial.
    
    rewrite Z_Z'_pred with (m := n).
    rewrite H. rewrite <- coercion_Z'_Z_Z'_id. trivial.
    symmetry. rewrite <- coercion_Z_Z'_Z_id. trivial.
    rewrite <- coercion_Z'_Z_Z'_id.
    apply Int_Int'_coercion_equiv. symmetry. trivial.
  Qed.
  
  Lemma Z_Z'_eq_opp : forall (n : Int),
    Zopp n = Z'opp n.
  Proof.
    intros. induction n. trivial.
  Qed.
  
  Definition Zsign (n : Int') :=
  match n with
  | z0 => zero
  | zpos n' => succ zero
  | zneg n' => pred zero
  end.
  
  Lemma PosZ_pos : forall n, positive (zpos n).
  Proof.
    intros. induction n.
    apply (lte_id 1).
    rewrite <- Z'succ_zpos.
    rewrite <- Z_Z'_succ with (n := zpos n).
    apply lte_s, IHn. reflexivity.
    rewrite <- coercion_Z'_Z_Z'_id. reflexivity.
  Qed.
  
  Theorem abs_product_Zsign : forall (n : Int'), abs n = n * (Zsign n).
  Proof.
    intros. destruct_sign n.
    trivial. destruct n.
    simpl.
  Qed.
  
  Theorem pos_zpos : forall n, positive n <-> exists m, n = zpos m.
  Proof.
    split. intro. induction H.
    exists pz_one. trivial.
    destruct IHlte. exists (pz_succ x).
    rewrite <- Z'succ_zpos, H0. trivial.
    
    intro. destruct H. induction x.
    simpl in H. rewrite H. apply (lte_id 1).
    rewrite H, <- Z'succ_zpos.
    rewrite <- Z_Z'_succ with (n := zpos x).
    apply lte_s.
  Qed.
  
  
  Record Q : Set := Q_make {Q_num : Int; Q_den : PosZ}.
  
  Declare Scope Q_scope.
  Delimit Scope Q_scope with Q.
  Bind Scope Q_scope with Q.
  Open Scope Q_scope.
  
  Infix "a # b" := (Q_make a b) (at level 55, no associativity) : Q_scope.
  
  Definition inject_Int_Q (n : Int) : Q := Q_make n pz_one.
  
  Coercion inject_Int_Q : Int >-> Q.
  
  Definition Q_eq (p q : Q) := (Q_num p * Q_den q) = (Q_num q * Q_den p).
  Definition Q_lte (p q : Q) := lte (Q_num p * Q_den q) (Q_num q * Q_den p).
  Definition Q_lt (p q : Q) := lt (Q_num p * Q_den q) (Q_num q * Q_den p).
  Definition Q_gte (p q : Q) := gte (Q_num p * Q_den q) (Q_num q * Q_den p).
  Definition Q_gt (p q : Q) := gt (Q_num p * Q_den q) (Q_num q * Q_den p).
  
  Infix "==" := Q_eq (at level 70, no associativity) : Q_scope.
  Infix "<" := Q_lt : Q_scope.
  Infix "<=" := Q_lte : Q_scope.
  Notation "x > y" := (Q_lt y x)(only parsing) : Q_scope.
  Notation "x >= y" := (Q_lte y x)(only parsing) : Q_scope.
  Notation "x <= y <= z" := (x<=y/\y<=z) : Q_scope.
  Notation "x <= y < z" := (x<=y/\y<z) : Q_scope.
  Notation "x < y <= z" := (x<y/\y<=z) : Q_scope.
  Notation "x < y < z" := (x<y/\y<z) : Q_scope.
  
  Hint Unfold Q_eq Q_lt Q_lte : hdb.
  
  Theorem Q_identity_weak : forall (p : Q), p == Q_make (Q_num p) (Q_den p).
  Proof.
    intro. unfold Q_eq. simpl. reflexivity.
  Qed.
  
  Lemma inject_Int_Q_injection : forall a b : Int, a == b -> a = b.
  Proof.
    intros a b H. unfold Q_eq in H. simpl in H.
    repeat rewrite multiply_id_r in H. assumption.
  Qed.
  
  Lemma Q_cancellation_l : forall (a : Int) (b m : PosZ),
    (Q_make a b) == (Q_make (m * a) (PosZmultiply m b)).
  Proof.
    intros. unfold Q_eq. simpl.
    rewrite PosZmultiply_Zmultiply_coincide. ring.
  Qed.
  
  Lemma Q_eq_refl : forall (p : Q), p == p.
  Proof.
    auto with hdb.
  Qed.
  
  Lemma Q_eq_symm : forall (p q : Q), p == q -> q == p.
  Proof.
    auto with hdb.
  Qed.
  
  Lemma Q_eq_trans : forall (p q r : Q), p == q -> q == r -> p == r.
  Proof.
    unfold Q_eq. intros p q r H G.
    apply eq_multiply_implies_eq_l with (k := Q_den q).
    apply PosZ_not_Int_zero.
    transitivity (Q_num p * Q_den q * Q_den r); try ring.
    rewrite H.
    transitivity (Q_num q * Q_den r * Q_den p); try ring.
    rewrite G.
    ring.
  Qed.
  
  Hint Resolve Q_eq_refl : hdb.
  Hint Resolve Q_eq_symm : hdb.
  Hint Resolve Q_eq_trans : hdb.
  
  Instance Q_Setoid : Equivalence Q_eq.
  Proof.
    split; red; eauto with hdb.
  Qed.
  
  Definition Q_add (p q : Q) :=
    Q_make ((Q_num p) * (Q_den q) + (Q_num q) * (Q_den p))
           (PosZmultiply (Q_den p) (Q_den q)).
  
  Definition Q_mul (p q : Q) :=
    Q_make ((Q_num p) * (Q_num q)) (PosZmultiply (Q_den p) (Q_den q)).
    
  Definition Q_sub (p q : Q) :=
    Q_make ((Q_num p) * (Q_den q) - (Q_num q) * (Q_den p))
           (PosZmultiply (Q_den p) (Q_den q)).
  
  Definition Q_opp (p : Q) := Q_make (- (Q_num p)) (Q_den p).
  
  Definition Q_inv (p : Q) := 
  match Q_num p with
  | zero => zero
  | _ => match
  end.
  
  Definition Q_div (p q : Q) := Q_mul p (Q_inv q).
  
  Infix "⊕" := Q_add (at level 50, no associativity) : Q_scope.
  Infix "⊗" := Q_mul (at level 50, no associativity) : Q_scope.
  Notation "- p" := (Q_opp p).
  
  Lemma Q_add_id_r : forall p : Q, p ⊕ 0 = p.
  Proof.
    intros. unfold Q_add. simpl.
    repeat rewrite multiply_id_r. rewrite add_zero_r.
    symmetry. apply Q_identity.
    
  Qed.
  
  
  
  
  
  