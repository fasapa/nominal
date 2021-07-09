From Nominal Require Import Perm.

Section ProperPermFun.
  Context (A B: Type) `{Perm A, Perm B}.
  
  Record proper_perm_fun : Type := ProperPermFun {
    fproper :> A → B;
(*  f_to : Perm A;
    f_from : Perm B; *)
    fproper_spec : Proper ((≡@{A}) ⟹ (≡@{B})) fproper
  }.
End ProperPermFun.

Arguments ProperPermFun {_ _ _ _} _ {_}.
Existing Instance fproper_spec.

Notation "'λp' x .. y , t" :=
  (@ProperPermFun _ _ _ _ (λ x, .. (@ProperPermFun _ _ _ _ (λ y, t) _) ..) _)
  (at level 200, x binder, y binder, right associativity).
  
Notation " A ⇥ B " := (proper_perm_fun A B) (at level 99, B at level 200, right associativity).

Section proper_perm_fun.
  Context `{Perm A, Perm B}.
  
  #[global] Instance perm_fun_proper (f: A ⇥ B): Proper ((≡@{A}) ⟹ (≡@{B})) f.
  Proof. apply fproper_spec. Qed.

  #[global] Instance perm_fun_proper_equiv: Equiv (A ⇥ B) := 
    λ f g, ∀ (a : A), f a ≡@{B} g a.

  #[global] Instance perm_fun_proper_equivalence : Equivalence perm_fun_proper_equiv.
  Proof. split; repeat intro; [reflexivity | symmetry | etransitivity]; eauto. Qed.

  #[global] Instance: Proper (perm_fun_proper_equiv ⟹ (≡@{A}) ⟹ (≡@{B})) (fproper A B).
  Proof. repeat intro; rewrite H4; auto. Qed.

  #[global,refine] Instance perm_fun_proper_act : PermAct (A ⇥ B) :=
    λ p (f: A ⇥ B), (λp (a : A), p • f(-p • a)).
  Proof.
    - assumption.
    - assumption.
    - typeclasses eauto.
    - repeat intro; apply gact_proper.
      + reflexivity.
      + apply fproper_spec; apply gact_proper; auto.  
  Defined. 

  #[global] Instance perm_fun_proper_perm: Perm (A ⇥ B).
  Proof. split.
    - apply perm_fun_proper_equivalence.
    - intros ? ? EE f g EF ?; simpl; rewrite EE, EF; auto. 
    - unfold equiv, perm_fun_proper_equiv; intros; simpl;
        rewrite gact_id, grp_inv_neutral, gact_id; reflexivity.
    - unfold equiv, perm_fun_proper_equiv; intros; simpl;
        rewrite <-perm_op_inv, 2!gact_compat; reflexivity.
  Qed.
End proper_perm_fun.