(*
    Proof of Correctness of Insertion Sort from scratch
    Only assumptions include existence of a type with
    a decidable ordering that is transitive and antisymmetric.
    
    Last updated 28th December 2021
*)

Section Sorting.
  Inductive list {T : Type} : Type :=
  | nil_list : list
  | cons_list : T -> list -> list.
  
  Inductive Bool : Set :=
  | false : Bool
  | true : Bool.
  
  Inductive True : Prop :=
  | yes : True.
  
  Register True as core.True.type.
  
  Inductive False : Prop :=.
  
  Register False as core.False.type.
  
  Definition is_true (b : Bool) :=
  match b with
  | true => True
  | false => False
  end.
  
  Inductive inhabited (T : Type) : Prop := inhabits : T -> inhabited T. 
  
  Lemma prop_eq_iff : forall (P Q : Prop), P = Q -> (P <-> Q).
  Proof.
    split. all: intro. 
    rewrite H in H0. trivial. 
    rewrite <- H in H0. trivial.
  Qed.
  
  Lemma forall_and : forall {T : Type}(P Q : T -> Prop),
    (forall t : T, P t /\ Q t) <-> 
    (forall t : T, P t) /\ (forall t : T, Q t).
  Proof.
    split. intro. split. apply H. apply H.
    intros. destruct H as [H G]. split. apply (H t). apply (G t).
  Qed.
  
  Lemma diff_true_false : true <> false.
  Proof. 
    intro. apply f_equal with (f := fun t => is_true t) in H.
    simpl in H. apply prop_eq_iff in H. destruct H. contradiction.
  Qed.
  
  Lemma diff_false_true : false <> true.
  Proof.
    intro. symmetry in H. apply diff_true_false in H. contradiction.
  Qed.
  
  Definition diff_bool : true <> false /\ false <> true.
  Proof.
    split. apply diff_true_false. apply diff_false_true.
  Qed.
  
  Inductive Nat : Set :=
  | zero : Nat
  | succ : Nat -> Nat.
  
  Theorem zero_not_succ : forall (n : Nat), succ n <> zero.
  Proof.
    set (N2B (n : Nat) := match n with | succ n' => true | zero => false end).
    intro. induction n. 
    all: intro; apply f_equal with (f := fun t => N2B t) in H;
    simpl in H; apply diff_bool in H; contradiction.
  Qed.
  
  Theorem nat_not_succ : forall (n : Nat), succ n <> n.
  Proof.
    intro. induction n. apply zero_not_succ.
    intro. inversion H. contradiction.
  Qed.
  
  Fixpoint add (n m : Nat) :=
  match n with
  | zero => m
  | succ n' => succ (add n' m)
  end.
  
  Lemma add_id_r : forall n, add n zero = n.
  Proof.
    intro. induction n. trivial.
    simpl. rewrite IHn. reflexivity.
  Qed.
  
  Lemma add_succ_r : forall n m, add n (succ m) = succ (add n m).
  Proof.
    intros. induction n. trivial.
    simpl. rewrite IHn. reflexivity.
  Qed.
  
  Lemma add_comm : forall n m, add n m = add m n.
  Proof.
    intros. induction m. rewrite add_id_r. trivial.
    simpl. rewrite add_succ_r, IHm. reflexivity.
  Qed.
  
  Fixpoint sum_over_list {T : Type} (f : T -> Nat) (l : list) :=
  match l with
  | nil_list => zero
  | cons_list a w => add (f a) (sum_over_list f w)
  end.
  
  Lemma nil_list_unique : forall {T : Type} (l : @list T) t, 
    (cons_list t l) <> nil_list.
  Proof.
    intros T l t H.
    apply f_equal with 
      (f := fun k => match k with | nil_list => true | _ => false end)
    in H.
    apply diff_bool, H.
  Qed. 
  
  Ltac destruct_bool := intros; destruct_all Bool; simpl in *; trivial; try discriminate.
  
  Lemma bool_decidability : forall (a b : Bool), {a = b} + {a <> b}.
  Proof.
    intros. destruct_bool.
    left. reflexivity. right. apply diff_bool.
    right. apply diff_bool. left. reflexivity.
  Qed.
  
  Lemma true_proof (P : Prop) : (True -> P) -> P.
  Proof.
    intro. exact (H yes).
  Qed.
  
  Definition band (a b : Bool) : Bool :=
  match a, b with
  | true, true => true
  | _, _ => false
  end.
  Infix "&&" := band (at level 40, left associativity).
  
  Definition bor (a b : Bool) : Bool :=
  match a, b with
  | true, _ => true
  | _, true => true
  | _, _ => false
  end.
  Infix "||" := bor (at level 50, left associativity).

  Inductive Permutation {T : Type} : @list T -> list -> Prop :=
  | perm_nil : Permutation nil_list nil_list
  | perm_skip : forall a x y, Permutation x y -> Permutation (cons_list a x) (cons_list a y)
  | perm_swap : forall a b x, Permutation (cons_list a (cons_list b x)) (cons_list b (cons_list a x))
  | perm_trans : forall x y z, Permutation x y -> Permutation y z -> Permutation x z.
  
  Definition perm_id : forall {T : Type} (l : @list T), Permutation l l.
  Proof.
    intro. induction l. exact perm_nil. exact (perm_skip t l l IHl).
  Qed.
  
  Definition perm_refl : 
    forall {T : Type} (x y : @list T), Permutation x y -> Permutation y x.
  Proof.
    intros. induction H. 
    exact perm_nil.
    apply (perm_skip a y x). assumption.
    apply (perm_swap b a x).
    apply (perm_trans z y x IHPermutation2 IHPermutation1).
  Qed.
  
  Fixpoint length {T : Type} (l : @list T) : Nat :=
  match l with
  | cons_list a w => succ (length w)
  | nil_list  => zero
  end.
  
  Lemma list_length_zero : forall {T : Type} (l : @list T), 
    length l = zero -> l = nil_list.
  Proof.
    intros. induction l. 
    reflexivity. simpl in H.
    apply zero_not_succ in H. contradiction.
  Qed.
  
  Theorem length_invar_perm : forall {T : Type} (x y : @list T), 
    Permutation x y -> (length x) = (length y).
  Proof.
    intros. induction H. reflexivity.
    simpl. rewrite IHPermutation. reflexivity.
    simpl. reflexivity.
    rewrite IHPermutation2 in IHPermutation1. assumption.
  Qed.
  
  Lemma perm_of_nil : 
    forall {T : Type} (l : @list T), Permutation l nil_list -> l = nil_list.
  Proof.
    intros. apply length_invar_perm in H. simpl in H.
    apply list_length_zero in H. assumption.
  Qed.
  
  Fixpoint All {T : Type} (P : T -> Prop) (l : list) : Prop :=
  match l with
  | nil_list => True
  | cons_list x w => (P x) /\ (All P w)
  end.
  
  Inductive Every {T : Type} (P : T -> Prop) : list -> Prop :=
  | every_nil : Every P nil_list
  | every_cons t l : Every P l -> P t -> Every P (cons_list t l).
  
  Theorem all_every_equiv : forall {T : Type} (P : T -> Prop) l,
    All P l -> Every P l.
  Proof.
    intros. induction l. exact (every_nil P).
    simpl in H. destruct H. apply IHl in H0.
    exact (every_cons P t l H0 H).
  Qed.
  
  Theorem every_all_equiv : forall {T : Type} (P : T -> Prop) l,
    Every P l -> All P l.
  Proof.
    intros. induction H. simpl. apply yes.
    simpl. split. apply H0. apply IHEvery.
  Qed.
  
  Lemma every_rem : forall {T : Type} (P : T -> Prop) t l,
  Every P (cons_list t l) -> Every P l.
  Proof.
    intros. apply every_all_equiv in H. simpl in H. destruct H.
    apply all_every_equiv in H0. apply H0.
  Qed.
  
  Lemma every_check : forall {T : Type} (P : T -> Prop) t l,
  Every P (cons_list t l) -> P t.
  Proof.
    intros. apply every_all_equiv in H. simpl in H.
    destruct H. apply H.
  Qed.
  
  Lemma every_expand : forall {T : Type} (P : T -> Prop) t l,
  Every P (cons_list t l) <-> (P t) /\ (Every P l).
  Proof.
    split. intro. split. apply every_all_equiv in H. simpl in H. destruct H.
    apply H. apply every_rem in H. apply H.
    intro. destruct H. apply (every_cons P t l).
    apply H0. apply H.
  Qed.
  
  Lemma all_in_perms : forall {T : Type} (P : T -> Prop) (x y : list),
    Permutation x y -> All P x -> All P y.
  Proof.
    intros.
    
    induction H. apply H0.
    simpl in H0. destruct H0. simpl. split.
    apply H0. apply (IHPermutation H1).
    
    simpl. repeat split. 
    all: simpl in H0; repeat destruct H0; trivial.
    
    apply (IHPermutation2 (IHPermutation1 H0)).
  Qed.
  
  (*Lemma perm_f_indpndnt : forall {T : Type} (f : @list T -> list) t l,
    Permutation l (f l) -> Permutation (cons_list t (f l)) (f (cons_list t l)).
  Proof.
    intros.
    induction l.
  Qed.*)
  
  Variable A : Type.
  Variable blt : A -> A -> Bool.
  Variable blt_antisym : forall (a b : A), blt a b = true <-> blt b a = false.
  Variable blt_trans : forall (a b c : A), ((blt a b) && (blt b c)) = (blt a c).
  
  (*Variable lt : A -> A -> Prop.
  Variable lt_antisym : forall (a b : A), lt a b <-> (lt b a -> False).
  Variable lt_blt_equiv : forall (a b : A), blt a b = true <-> lt a b.
  Variable lt_blt_antiequiv : forall (a b : A), blt a b = false <-> lt b a.
  Variable lt_decidability : forall (a b : A), 
    (lt a b /\ not (lt b a)) \/ (lt b a /\ not (lt a b)).*)
  
  Variable beq : A -> A -> Bool.
  Infix "==" := beq (at level 50, left associativity).
  
  Variable beq_refl : forall (a : A), a == a = true.
  
  (*Variable beq_symmetry : forall (a b : A), (a == b) = (b == a).

  Variable beq_transitivity : forall (a b c : A), 
    ((a == b) && (b == c)) = (a == c).*)
  
  Variable beq_eq : forall (a b : A), a == b = true -> a = b.
  
  Lemma blt_antirefl : forall (a : A), blt a a = false.
  Proof.
    intro. destruct (blt a a) eqn:H.
    reflexivity. apply blt_antisym in H as G.
    rewrite H in G. assumption.
  Qed.
  
  Lemma blt_decidability : forall (a b : A), {blt a b = true} + {blt a b = false}.
  Proof.
    intros. destruct (blt a b) eqn:H.
    right. reflexivity.
    left. reflexivity.
  Qed.
  
  Definition lt (a b : A) := blt a b = true.

  Lemma lt_antisym : forall (a b : A), lt a b <-> (lt b a -> False).
  Proof.
    split. unfold lt. intros. apply blt_antisym in H.
    rewrite H0 in H. apply diff_bool in H. contradiction.
    unfold lt. intros. apply blt_antisym.
    destruct (blt b a) eqn:G. reflexivity. contradiction.
  Qed.
  
  Lemma lt_decidability : forall (a b : A), 
    (lt a b /\ not (lt b a)) \/ (lt b a /\ not (lt a b)).
  Proof.
    intros. unfold lt. destruct (blt a b) eqn:H.
    right. split. apply blt_antisym in H. 
    apply H. apply diff_bool.
    left. split. 
    reflexivity. apply blt_antisym in H. rewrite H. apply diff_bool.
  Qed.
  
  Lemma lt_blt_equiv : forall (a b : A), blt a b = true <-> lt a b.
  Proof.
    split. intro. unfold lt. assumption. 
    intro. unfold lt in H. assumption.
  Qed.
  
  Lemma lt_blt_antiequiv : forall (a b : A), blt a b = false <-> lt b a.
  Proof.
    split. intro. unfold lt. apply blt_antisym. assumption.
    intro. unfold lt in H. apply blt_antisym. assumption.
  Qed.

  
  Lemma blt_inv (a b : A) : blt a b = true <-> blt b a = false.
  Proof.
    split. intro. apply lt_blt_equiv, lt_blt_antiequiv in H. apply H.
    intro. apply lt_blt_antiequiv, lt_blt_equiv in H. apply H.
  Qed.
  
  Fixpoint frequency (l : @list A) (t : A) :=
  match l with
  | nil_list => zero
  | cons_list r w => match t == r with
                     | true => succ (frequency w t)
                     | false => frequency w t
                     end
  end.
  
  Lemma frequency_cons : forall l t,
    frequency (cons_list t l) t = succ (frequency l t).
  Proof.
    intros. induction l. simpl. rewrite beq_refl. reflexivity.
    destruct (t == t0) eqn:Ht;
    simpl; rewrite Ht; rewrite beq_refl; reflexivity.
  Qed.
  
  Lemma frequency_succ : forall l t a,
    frequency (cons_list t l) a = succ (frequency l a) -> a == t = true.
  Proof.
    intros. destruct (a == t) eqn:G.
    unfold frequency in H. rewrite G in H. fold frequency in H.
    symmetry in H. apply nat_not_succ in H. contradiction.
    reflexivity.
  Qed.
  
  Lemma frequency_nil : forall l, (forall t, frequency l t = zero) <->
    l = nil_list.
  Proof.
    split. intros. induction l. reflexivity.
    
    exfalso. set (G := frequency (cons_list t l) t).
    assert (exists m, G = succ m).
    unfold G, frequency. rewrite beq_refl.
    fold frequency. exists (frequency l t). reflexivity.
    unfold G in H0. rewrite H in H0. destruct H0. symmetry in H0.
    apply (zero_not_succ x H0).
    
    intros.
    rewrite H. simpl. reflexivity.
  Qed.
  
  Definition Permutation' (x y : list):= forall (a : A),
    frequency x a = frequency y a.
  
  Lemma perm'_nil : Permutation' nil_list nil_list.
  Proof.
    unfold Permutation'. trivial.
  Qed.
  
  Lemma perm'_skip : forall (x y : list) (t : A),
    Permutation' x y -> Permutation' (cons_list t x) (cons_list t y).
  Proof.
    unfold Permutation'. intros.
    destruct (a == t) eqn:Ht;
    simpl; rewrite Ht; rewrite H; reflexivity.
  Qed.
  
  Lemma perm'_swap : forall (l : list) (a b : A),
    Permutation' (cons_list a (cons_list b l))
                 (cons_list b (cons_list a l)).
  Proof.
    unfold Permutation'. intros.
    destruct (a0 == a) eqn:Ha; destruct (a0 == b) eqn:Hb; simpl;
    rewrite Ha, Hb; reflexivity.
  Qed.
  
  Lemma perm'_trans : forall (x y z : list),
    Permutation' x y -> Permutation' y z -> Permutation' x z.
  Proof.
    unfold Permutation'. intros x y z Hxy Hyz a.
    rewrite Hxy, Hyz. reflexivity.
  Qed.
  
  Lemma perm'_of_nil : 
    forall (l : list), Permutation' l nil_list -> l = nil_list.
  Proof.
    intros. unfold Permutation' in H. simpl in H.
    apply frequency_nil in H. assumption.
  Qed.
  
  Theorem Permutation_Permutation'_coincide_r : forall x y,
    Permutation x y -> Permutation' x y.
  Proof.
    intros. induction H.
    
    apply perm'_nil.
    apply perm'_skip. assumption.
    apply perm'_swap.
    apply (perm'_trans x y z); assumption.
  Qed. (*Proving the reverse isn't possible with Permutation'*)
  
  Fixpoint contains {T : Type} (x : list) (t : T) : Prop :=
  match x with
  | nil_list => False
  | cons_list a y => t = a \/ contains y t
  end.
  
  Inductive contains' {T : Type} : list -> T -> Prop :=
  | contains_cons : forall (x : list) (t : T),
      contains' (cons_list t x) t
  | contains_cont : forall (x : list) (t a : T),
      contains' x t -> contains' (cons_list a x) t.
  
  Lemma contains_nil : forall {T : Type} (a : T),
    contains nil_list a -> False.
  Proof.
    intros. simpl in H. apply H.
  Qed.
  
  Lemma contains_singleton : forall {T : Type} (a t : T),
    contains (cons_list a nil_list) t -> t = a.
  Proof.
    intros. simpl in H. destruct H. apply H. contradiction.
  Qed.
  
  Lemma contains'_nil : forall {T : Type} (a : T),
    contains' nil_list a -> False.
  Proof.
    intros. inversion H as [x b Hl Ha | x b c Ha Hl Ht];
    apply f_equal with (f := fun t => length t) in Hl;
    simpl in Hl; apply zero_not_succ in Hl; contradiction.
  Qed.
  
  Lemma contains'_cons : forall {T : Type} (x : list) (a t : T),
    contains' (cons_list a x) t -> t = a \/ contains' x t.
  Proof.
    intros. inversion H as [l b Hx Heq | l b c Hcon Hx Heq].
    left; reflexivity. right; apply Hcon.
  Qed.
  
  Lemma contains'_cons_nil : forall {T : Type} (x : list) (a t : T),
    (contains' (cons_list a x) t -> False) -> (contains' x t -> False).
  Proof.
    intros. apply H. apply contains_cont. apply H0.
  Qed.
  
  Theorem contains_contains'_coincide : forall (x : list) (t : A),
    contains x t <-> contains' x t.
  Proof.
    split; intro; induction x.
    
    apply contains_nil in H. contradiction.
    destruct H as [Hl | Hr].
    rewrite Hl. apply contains_cons.
    apply contains_cont, (IHx Hr).
    
    apply contains'_nil in H. contradiction.
    inversion H as [w|w]. unfold contains. left. reflexivity.
    simpl. apply contains'_cons in H.
    destruct H as [Hl | Hr].
    left; apply Hl. right; apply (IHx Hr).
  Qed.
  
  Lemma contains_frequency_nil : forall (x : list) (a : A),
    (contains x a -> False) <-> frequency x a = zero.
  Proof.
    split; intros; induction x.
    
    trivial. destruct_bool. destruct (a == t) eqn:G.
    apply IHx. intro. apply H. right. apply H0.
    intuition. apply beq_eq, H0 in G. contradiction.
    
    apply contains_nil in H0. contradiction.
    simpl in H0. destruct (a == t) eqn:G.
    unfold frequency in H. rewrite G in H.
    fold frequency in H.
    destruct H0. rewrite H0, beq_refl in G.
    apply diff_true_false in G. contradiction.
    apply (IHx H H0).
    simpl in H. rewrite G in H. apply zero_not_succ in H.
    contradiction.
  Qed.
  
  Definition Permutation'' (x y : list) := forall (a : A),
    (contains x a <-> contains y a) /\ frequency x a = frequency y a.
  
  Lemma perm''_nil : Permutation'' nil_list nil_list.
  Proof.
    unfold Permutation''. intro. simpl.
    split; try split; trivial.
  Qed.
  
(* The following commented-out code is a work in progress.

  Lemma perm''_skip : forall (x y : list) (t : A),
    Permutation'' x y -> Permutation'' (cons_list t x) (cons_list t y).
  Proof.
    unfold Permutation''. intros. split. split.
    destruct (H a) as [Hc Hf].
    
    simpl. destruct (t == k) eqn:G.
    apply contains'_cons in Hy as G. destruct G.
    simpl. rewrite H0, beq_refl.
    apply f_equal with (f := fun t => succ t).
    apply (H k).
    
    destruct_bool; destruct (t == k) eqn:G.
    destruct Hx, Hy;
    try ((rewrite H0 in G || rewrite H1 in G); rewrite beq_refl in G;
    apply diff_true_false in G; contradiction).
    apply (H t H0 H1).
    
    apply f_equal with (f := fun t => succ t).
    apply (H t).
    destruct Hx.
  Qed.
  
  Lemma perm''_swap : forall (l : list) (a b : A),
    Permutation'' (cons_list a (cons_list b l))
                 (cons_list b (cons_list a l)).
  Proof.
    unfold Permutation'. intros.
    destruct (a0 == a) eqn:Ha; destruct (a0 == b) eqn:Hb; simpl;
    rewrite Ha, Hb; reflexivity.
  Qed.
  
  Lemma perm''_trans : forall (x y z : list),
    Permutation'' x y -> Permutation'' y z -> Permutation'' x z.
  Proof.
    unfold Permutation''. intros x y z Hxy Hyz a.
    rewrite Hxy, Hyz. reflexivity.
  Qed.
  
  Lemma perm''_of_nil : 
    forall (l : list), Permutation'' l nil_list -> l = nil_list.
  Proof.
    intros. unfold Permutation' in H. simpl in H.
    apply frequency_nil in H. assumption.
  Qed.
  
  Theorem Permutation'_Permutation''_coincide : forall (x y : list),
    Permutation' x y <-> Permutation'' x y.
  Proof.
    split; intro. induction y.
    apply perm'_of_nil in H. rewrite H.
  Qed.
  *)
  
  Inductive Sorted : list -> Prop :=
  | nil_sorted : Sorted (nil_list)
  | singleton_sorted a : Sorted (cons_list a (nil_list))
  | list_sorted a b l : Sorted (cons_list b l) -> lt a b 
    -> Sorted (cons_list a (cons_list b l)).
  
  Fixpoint Sorted' (l : list) :=
  match l with
  | nil_list => True
  | cons_list a x => match x with
                     | nil_list => True
                     | cons_list b y => (lt a b) /\ Sorted' x
                     end
  end.
  
  Lemma Sorted_rem (l : list) : forall (a : A), 
    Sorted (cons_list a l) -> Sorted l.
  Proof.
    intros. inversion H.
    apply f_equal with (f := fun t => length t) in H0.
    simpl in H0. symmetry in H0. apply zero_not_succ in H0.
    contradiction.
    exact nil_sorted.
    assumption.
  Qed.
  
  Lemma Sorted'_rem (l : list) : forall (a : A),
    Sorted' (cons_list a l) -> Sorted' l.
  Proof.
    intros. induction l. trivial. 
    simpl in H. destruct H as [lt S'bl].
    induction l. trivial. apply S'bl.
  Qed.
  
  Theorem Sorted_Sorted'_coincide : forall l, Sorted l <-> Sorted' l.
  Proof.
    split.
    intro. induction H.
    all: simpl; try apply yes.
    split. assumption.
    induction l. apply yes.
    split. simpl in IHSorted.
    destruct IHSorted as [lt S'tl].
    apply lt. apply Sorted'_rem in IHSorted. assumption.
    
    intro. induction l. exact nil_sorted.
    induction l. exact (singleton_sorted t).
    apply Sorted'_rem in H as G.
    apply IHl in G. simpl in H. destruct H as [lt S't0l].
    apply (list_sorted t t0 l G lt).
  Qed.
  
  Definition Is_Sorting_Algorithm (f : list -> list) := 
    forall (l : list), (Sorted (f l) /\ Permutation l (f l)).
  
  Fixpoint insertion (n : A) (l : list) :=
  match l return list with
  | nil_list => cons_list n nil_list
  | cons_list h k => if blt h n then
                       cons_list n (cons_list h k)
                       else cons_list h (insertion n k)
  end.
  
  Fixpoint insertion_sort (l : list) :=
  match l with
  | nil_list => l
  | cons_list h k => insertion h (insertion_sort k)
  end.
  
  Lemma insertion_into_sorted_is_sorted : forall (l : list) (a : A),
    Sorted l -> Sorted (insertion a l).
  Proof.
    intros l a S. induction S; simpl. exact (singleton_sorted a).
    
    destruct (blt a0 a) eqn:H. 
    apply lt_blt_antiequiv in H.
    exact (list_sorted a a0 nil_list (singleton_sorted a0) H).
    apply lt_blt_equiv in H.
    exact (list_sorted a0 a nil_list (singleton_sorted a) H).
    
    destruct (blt a0 a) eqn:G.
    apply lt_blt_antiequiv in G.
    exact (list_sorted a a0 (cons_list b l) (list_sorted a0 b l S H) G).
    
    destruct (blt b a) eqn:K.
    apply lt_blt_equiv in G. apply lt_blt_antiequiv in K.
    exact (list_sorted a0 a (cons_list b l) (list_sorted a b l S K) G).
    apply lt_blt_equiv in G, K. 
    unfold insertion in IHS.
    destruct (blt b a) eqn:L in IHS.
    apply lt_blt_antiequiv in L.
    
    exfalso.
    destruct (lt_decidability a b) as [dl | dr].
    destruct dl as [x y]. contradiction.
    destruct dr as [x y]. contradiction.
    
    fold insertion in IHS.
    exact (list_sorted a0 b (insertion a l) IHS H).
  Qed.
  
  Lemma insertion_into_is_perm_of_cons : forall (a : A) (l : list),
    Permutation (cons_list a l) (insertion a l).
  Proof.
    intros.
    
    induction l.
    simpl. exact (perm_skip a nil_list nil_list perm_nil).
    
    unfold insertion. destruct (blt t a) eqn:H.
    exact (perm_id (cons_list a (cons_list t l))). fold insertion.
    
    set (x := cons_list a (cons_list t l)).
    set (y := cons_list t (cons_list a l)).
    set (z := cons_list t (insertion a l)).
    set (K := perm_swap a t l).
    set (G := perm_skip t (cons_list a l) (insertion a l) IHl).
    apply (perm_trans x y z K G).
  Qed.
  
  Theorem Insertion_Sort_Is_Sorting_Alg : Is_Sorting_Algorithm insertion_sort.
  Proof.
    unfold Is_Sorting_Algorithm. intros.
    
    induction l. simpl. split. exact nil_sorted. exact perm_nil.
    destruct IHl as [Hs Hp].
    split. simpl. apply insertion_into_sorted_is_sorted.
    assumption.
    
    simpl. apply (perm_skip t l (insertion_sort l)) in Hp.
    
    set (x := cons_list t l).
    set (y := cons_list t (insertion_sort l)).
    set (z := insertion t (insertion_sort l)).
    set (G := insertion_into_is_perm_of_cons t (insertion_sort l)).
    apply (perm_trans x y z Hp G).
  Qed.
  
  Definition clear_list (l : @list A):= @nil_list A.
  
  Lemma Clear_List_Sorts : forall (l : list), 
    Sorted (clear_list l).
  Proof.
    intros. unfold clear_list. apply nil_sorted.
  Qed.
  
  Lemma Clear_List_Not_Permutes : forall (l : list), 
    l <> nil_list -> Permutation l (clear_list l) -> False.
  Proof.
    intros. destruct l. contradiction.
    unfold clear_list in H0.
    apply perm_of_nil in H0. contradiction.
  Qed.
  
  Theorem Clear_List_Not_Sorting_Alg : inhabited A -> Is_Sorting_Algorithm clear_list -> False.
  Proof.
    unfold Is_Sorting_Algorithm. intros Hin H.
    apply forall_and in H. destruct H as [H G].
    inversion Hin as [a].
    set (l := cons_list a nil_list).
    assert (l <> nil_list) as Heq by (apply nil_list_unique).
    set (Hn := G l).
    apply (Clear_List_Not_Permutes l Heq Hn).
  Qed.
  
  
  
  
  
  
  
  