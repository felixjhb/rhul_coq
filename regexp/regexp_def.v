Require Import Bool Coq.Strings.Ascii Coq.Lists.List.

Section regexp_def.

    Definition string := list ascii.

    Inductive regexp : Type :=
    | Eps : regexp
    | Concat : regexp -> regexp -> regexp
    | Or : regexp -> regexp -> regexp
    | Star : regexp -> regexp
    | Char : ascii -> regexp.

    Definition Plus (A : regexp) : regexp := Concat A (Star A).

    Inductive re_spec : regexp -> string -> Prop :=
    | rs_eps : re_spec Eps nil
    | rs_concat : forall E E' s s',
        re_spec E s -> re_spec E' s' -> re_spec (Concat E E') (s ++ s')
    | rs_or : forall E E' s, (re_spec E s) + (re_spec E' s) -> re_spec (Or E E') s
    | rs_star_eps : forall E, re_spec (Star E) nil
    | rs_star_one : forall E s, re_spec E s -> re_spec (Star E) s
    | rs_star_many : forall E s s', 
        re_spec (Star E) s -> re_spec (Star E) s' -> re_spec (Star E) (s ++ s')
    | rs_char : forall a, re_spec (Char a) (cons a nil).

    (* re_sub E E' : Prop
    Defines a partial ordering on regular expressions
    via language given by E contains language given by E'
    *)

    Inductive re_sub (E E' : regexp) : Prop :=
    | resub : (forall s, re_spec E' s -> re_spec E s) -> re_sub E E'.

    Definition re_eq (E E' : regexp) : Prop := re_sub E E' /\ re_sub E' E.

    Theorem re_sub_reflexivity : forall E, re_sub E E.
    Proof.
        induction E; apply resub; intros; assumption.
    Qed.

    Theorem re_sub_transitivity : forall E E' E'',
        re_sub E E' -> re_sub E' E'' -> re_sub E E''.
    Proof.
        intros. destruct H, H0. apply resub.
        intros. apply H, H0, H1.
    Qed.

    Corollary re_eq_reflexivity : forall E, re_eq E E.
    Proof.
        intro. unfold re_eq. split; apply re_sub_reflexivity.
    Qed.

    Corollary re_eq_transitivity : forall E E' E'',
        re_eq E E' -> re_eq E' E'' -> re_eq E E''.
    Proof.
        unfold re_eq. intros. destruct H, H0. split.
        - apply (re_sub_transitivity E E' E'' H H0).
        - apply (re_sub_transitivity E'' E' E H2 H1).
    Qed.

    Corollary re_eq_symmetry : forall E E', re_eq E' E <-> re_eq E E'.
    Proof.
        unfold re_eq. intros E E'. apply and_comm.
    Qed.

    (* dfa State Alphabet : Type
    Simulates a deterministic finite state automata.
    Record type containing an initial state,
    a function to check if a state is final,
    and a function to transition to the next state
    *)
    Record dfa {S A : Type} := DFA {
        initial_state : S;
        is_final : S -> bool;
        next : S -> A -> S
    }.

    Definition run_dfa S A (M : @dfa S A) (l : list A) : bool :=
        (is_final M) (fold_left (next M) l (initial_state M)).

    Definition redfa_Eps : @dfa bool ascii :=
        {|
        initial_state := true;
        is_final (s : bool) := 
            match s with
            | true => true
            | _ => false
            end;
        next (s : bool) (a : ascii) :=
            match s, a with
            | _, _ => false
            end;
        |}.
    
    Definition redfa_Concat S S' (M : @dfa S ascii) (M' : @dfa S' ascii) : @dfa (sum S S') ascii :=
        {|
        initial_state := inl (initial_state M);
        is_final (s : sum S S') :=
            match s with
            | inl _ => false
            | inr s' => (is_final M') s'
            end;
        next (s : sum S S') (a : ascii) :=
            match s with
            | inl s' =>
                match (is_final M) s' with
                | true => inr ((next M') (initial_state M') a)
                | false => inl ((next M) s' a)
                end
            | inr s' => inr ((next M') s' a)
            end;
        |}.

    Definition redfa_Or S S'(M : @dfa S ascii) (M' : @dfa S' ascii) : @dfa (prod S S') ascii :=
        {|
        initial_state := pair (initial_state M) (initial_state M');
        is_final (sp : prod S S') :=
            match sp with
            | pair s s' => (is_final M s) || (is_final M' s')
            end;
        next (sp : prod S S') (a : ascii) :=
            match sp with
            | pair s s' => pair (next M s a) (next M' s' a)
            end;
        |}.
    
    Definition redfa_Star S (M : @dfa S ascii) : @dfa S ascii :=
        {|
        initial_state := (initial_state M);
        is_final := (is_final M);
        next (s : S) (a : ascii) :=
            match (is_final M s) with
            | true => (next M) (initial_state M) a
            | false => (next M) s a
            end;
        |}.
    
    Definition redfa_Char (c : ascii) : @dfa bool ascii :=
        {|
        initial_state := false;
        is_final (s : bool) := s;
        next (s : bool) (a : ascii) :=
            match s, eqb a c with
            | false, true => true
            | _, _ => false
            end;
        |}. 

End Section.