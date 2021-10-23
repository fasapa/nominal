From Nominal Require Import Perm.

Section ProperPermFun.
  Context (A B: Type) `{Equiv A, Equiv B}.
  
  Record FunProper: Type := mkFunProper {
    fproper :> A → B;
    fproper_spec: Proper ((≡@{A}) ⟹ (≡@{B})) fproper
  }.
End ProperPermFun.

Arguments mkFunProper {_ _ _ _} _ {_}.
Existing Instance fproper_spec.

Notation "'λₚ' x .. y , t" :=
  (@mkFunProper _ _ _ _ (λ x, .. (@mkFunProper _ _ _ _ (λ y, t) _) ..) _)
  (at level 200, x binder, y binder, right associativity).
  
Notation " A '→ₚ' B " := (FunProper A B) (at level 99, B at level 200, right associativity).

Section ProperFunEquiv.
  Context `{Equiv A, Equiv B, !Equivalence (≡@{A}), !Equivalence (≡@{B})}.
  
  (* #[global] Instance: (f: A ⇥ B): Proper ((≡@{A}) ⟹ (≡@{B})) f.
  Proof. apply fproper_spec. Qed. *)

  #[global] Instance fun_proper_equiv: Equiv (A →ₚ B) := 
    λ f g, ∀ (a : A), f a ≡@{B} g a.

  #[global] Instance fun_proper_equivalence: Equivalence fun_proper_equiv.
  Proof. split; repeat intro; [reflexivity | symmetry | etransitivity]; eauto. Qed.

  #[global] Instance: Proper (fun_proper_equiv ⟹ (≡@{A}) ⟹ (≡@{B})) (fproper A B).
  Proof. repeat intro; rewrite H2; auto. Qed.
End ProperFunEquiv.

Section ProperFunPerm.
  Context `{Perm A, Perm B}.

  #[global,refine] Instance fun_proper_act: PermAct (A →ₚ B) :=
    λ p (f: A →ₚ B), (λₚ (a: A), p • f(-p • a)).
  Proof. 
    all:try (assumption || typeclasses eauto);
    repeat intro; rewrite H3; reflexivity. 
  Defined. 

  #[global] Instance FunProperPerm: Perm (A →ₚ B).
  Proof. 
    split.
      - apply fun_proper_equivalence.
      - intros ? ? EE f g EF ?; simpl; rewrite EE, EF; auto. 
      - unfold equiv, fun_proper_equiv; intros; simpl;
          rewrite gact_id, grp_inv_neutral, gact_id; reflexivity.
      - unfold equiv, fun_proper_equiv; intros; simpl;
          rewrite <-perm_op_inv, 2!gact_compat; reflexivity.
  Qed.
End ProperFunPerm.