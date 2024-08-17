From Nominal Require Import Nominal NameAbstraction.

Section Concretion.
    Context `{Nominal X}.

    Definition concretion (F: [𝔸]X) (b: Name): option X :=
       let (a,x) := abs F in
       if (decide (a = b)) then Some x else
       if (decide (b ∉ support x)) then Some (⟨a,b⟩ • x)
       else None.
    
    Lemma concretion_eq a b (x: X): 
        a = b → concretion ([a]x) b ≡ Some x.
    Proof. 
        intros; subst; unfold concretion; simpl; destruct (decide _); subst;
        [reflexivity | congruence].
    Qed.

    Lemma concretion_notin a b (x: X): 
        a ≠ b → b ∉ support x → concretion ([a]x) b ≡ Some (⟨a,b⟩ • x).
    Proof. 
        intros; subst; unfold concretion; simpl; destruct (decide _); subst;
        [congruence | destruct (decide _); [reflexivity | set_solver]]. 
    Qed.
    
End Concretion.