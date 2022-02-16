Section Exercises1.
  Inductive Nat : Set :=
  | zero : Nat
  | succ : Nat -> Nat.
  
  Inductive Bool : Set :=
  | false : Bool
  | true : Bool.
  
  Definition pred (n : Nat) :=
  match n with
  | zero => zero
  | succ u => u
  end.
  
  Definition ite (test : Bool) (f: Nat) (g : Nat) :=
  match test with
  | true => f
  | false => g
  end.
  
  Fixpoint lte (n : Nat) (m: Nat) :=
  match n, m with
  | zero, _ => true
  | _, zero => false
  | succ n', succ m' => lte n' m'
  end.
  
  Inductive vector (A : Type) : Nat -> Type :=
  | nil_vector : vector A zero
  | cons_vector : forall (n : Nat), A -> vector A n -> vector A (succ n).
  
  Inductive list (A : Type) : Type :=
  | nil_list : list A
  | cons_list : A -> list A -> list A.
   
  Fixpoint insertion (n : Nat) (l : list Nat) :=
  match l return list Nat with
  | nil_list _ => cons_list Nat n (nil_list Nat)
  | cons_list _ h k => match (lte h n) with
                       | true => cons_list Nat n (cons_list Nat h k)
                       | false => cons_list Nat h (insertion n k)
                       end
  end.
  
  Fixpoint insertion_sort (l : list Nat) :=
  match l with
  | nil_list _ => l
  | cons_list _ h k => insertion h (insertion_sort k)
  end.
  
  Definition safe_header (A : Type) (n : Nat) (v : vector A (succ n)) :=
  match v with
  | cons_vector _ n a w => a
  end.
  
  
  