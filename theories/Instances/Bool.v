From Nominal Require Import Nominal SupportedFunctions.

#[export] Instance bool_action: PermAction bool := λ p b, b.
#[export] Instance bool_equiv: Equiv bool := eq.
#[export] Instance bool_support: Support bool := λ b, ∅.

#[export] Instance bool_permT: PermT bool.
Proof.
    split; unfold equiv,bool_equiv,action,bool_action in *; auto; repeat intro.
    - typeclasses eauto.
    - subst; reflexivity.
Qed.

#[export] Instance bool_nominal: Nominal bool.
Proof. 
    split; intros; [apply bool_permT | unfold action,bool_action; reflexivity].
Qed.

(* Section Properties.
    Context `{Nominal X} (f: X →ₛ bool).

    Lemma lol: ∀ p x, (p•f) x = f (- p • x).
    Proof. unfold equiv,fun_supp_equiv; intros; rewrite fsupp_action.
        unfold action at 1; unfold bool_action. reflexivity.
    Qed.
    
End Properties. *)