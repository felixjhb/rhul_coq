Section Inj_Subtyping.
    Record Subtype (A B : Type) := subtype{
        injBA : B -> A;
        redAB : A -> option B;
        subtypeCond : forall (b : B), redAB (injBA b) = Some b;
        parentCond : forall (a : A), (exists (b : B), redAB a = Some b -> injBA b = a) \/ redAB a = None
    }.

    Parameter A : Type.
    Parameter B : Type.
    Parameter subAB : Subtype A B.

Section End.