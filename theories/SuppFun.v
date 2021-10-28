From Nominal Require Import Nominal.

Section SupportedFunctions.
  Context (X Y: Type) `{Nominal X, Nominal Y}.

  Record FunSupp: Type := mkFunSupp {
    f_car :> X → Y;
    f_supp: nameset; (* Function support *)
    f_proper: Proper ((≡@{X}) ⟹ (≡@{Y})) f_car;
    f_supp_spec: ∀ (a b: name), a ∉ f_supp → b ∉ f_supp →
        ∀ (x: X), (⟨a,b⟩ • (f_car (⟨a,b⟩ • x))) ≡@{Y} f_car x 
  }.
End SupportedFunctions.

Arguments mkFunSupp {_ _ _ _ _ _} _ _ {_ _}.
Arguments f_supp {_ _ _ _ _ _} _.
Existing Instance f_proper.

Notation "'λₛ' x .. y , t" :=
  (@mkFunSupp _ _ _ _ _ _ (λ x, .. (@mkFunSupp _ _ _ _ _ _ (λ y, t) _ _ _) ..) _ _ _)
  (at level 200, x binder, y binder, right associativity).

Notation " A '→ₛ' B " := (FunSupp A B) (at level 99, B at level 200, right associativity).

Section FunSuppProperties.
    Context `{Nominal X, Nominal Y}.
    
    #[global] Instance fun_supp_equiv: Equiv (X →ₛ Y) := λ f g, ∀ (x: X), f x ≡@{Y} g x.
    #[global] Instance fun_supp_equiv_equivalence: Equivalence fun_supp_equiv.
    Proof. split; repeat intro; [reflexivity | symmetry | etransitivity]; eauto. Qed.

    #[global] Instance: Proper (fun_supp_equiv ⟹ (≡@{X}) ⟹ (≡@{Y})) (f_car X Y).
    Proof. intros ? ? HH1 ? ? HH2; rewrite HH2; apply HH1. Qed.

    #[global,refine] Instance fun_supp_act: PermAct (X →ₛ Y) :=
      λ p (f: X →ₛ Y), (λₛ (x: X), p • f(-p • x)).
    Proof. 
      all:try (assumption || typeclasses eauto).
      - exact ((f_supp f) ∪ (perm_dom p)).
      - intros ? ? HH; rewrite HH; reflexivity.
      - intros; rewrite perm_comm; [apply perm_inj | set_solver | set_solver];
        (* see https://github.com/coq/coq/issues/8872 *)
        setoid_rewrite <-perm_comm; [rewrite f_supp_spec | apply perm_dom_inv | apply perm_dom_inv];
        set_solver.
    Defined. 

    #[global] Instance fun_supp_perm: Perm (X →ₛ Y).
    Proof.
      split.
      - apply fun_supp_equiv_equivalence.
      - intros ? ? EE f g EF ?; simpl; rewrite EE, EF; reflexivity.
      - unfold equiv, fun_supp_equiv; intros; simpl; rewrite gact_id, grp_inv_neutral, gact_id;
        reflexivity.
      - unfold equiv, fun_supp_equiv; intros; simpl; rewrite <-perm_op_inv, 2!gact_compat;
        reflexivity.
    Qed.

    #[global] Instance fun_supp_support: Support (X →ₛ Y) := λ fs, f_supp fs.

    #[global] Instance fun_supp_nominal: Nominal (X →ₛ Y).
    Proof.
      split.
      - apply fun_supp_perm.
      - intros f ? ? ? x; unfold support, fun_supp_support, action, prmact, fun_supp_act, equiv, fun_supp_equiv in *;
        simpl; intros; rewrite <-perm_inv; apply f_supp_spec; assumption.
    Qed.
End FunSuppProperties.
