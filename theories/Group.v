From Nominal Require Export Prelude.

(** *Group operations *)
Class Neutral A := neutral : A.
#[global] Hint Mode Neutral ! : typeclass_instances.
Notation ɛ := neutral.
Notation "ɛ@{ A }" := (@neutral A _) (only parsing) : nominal_scope.

Class Operator A := op: A → A → A.
#[global] Hint Mode Operator ! : typeclass_instances.
Instance: Params (@op) 2 := {}.

Infix "+" := op : nominal_scope.
Notation "(+)" := op (only parsing) : nominal_scope.
Notation "(+ x )" := (op x) (only parsing) : nominal_scope.
Notation "( x +)" := (λ y, op y x) (only parsing) : nominal_scope.

Class Inverse A := inv: A → A.
#[global] Hint Mode Inverse ! : typeclass_instances.
Instance: Params (@inv) 1 := {}.

Notation "- x" := (inv x) : nominal_scope.
Notation "(-)" := inv (only parsing) : nominal_scope.
Notation "x - y" := (x + (-y))%nom : nominal_scope.

Class Group (A : Type) `{Ntr: Neutral A, Opr: Operator A, Inv: Inverse A, Equiv A} : Prop := {
  grp_setoid :> Equivalence(≡@{A});
  grp_op_proper :> Proper ((≡@{A}) ⟹ (≡@{A}) ⟹ (≡@{A})) (+);
  grp_inv_proper :> Proper ((≡@{A}) ⟹ (≡@{A})) (-);

  grp_assoc : ∀ (x y z : A), x + (y + z) ≡@{A} (x + y) + z;

  grp_left_id : ∀ (x : A), ɛ@{A} + x ≡@{A} x;
  grp_right_id : ∀ (x : A), x + ɛ@{A} ≡@{A} x;

  grp_left_inv : ∀ (x : A), (-x) + x ≡@{A} ɛ@{A};
  grp_right_inv : ∀ (x : A), x - x ≡@{A} ɛ@{A};
}.
(* #[global] Hint Mode Group ! - - - -: typeclass_instances. *)

Arguments grp_assoc {_ _ _ _ _ Grp} : rename.
Arguments grp_left_id {_ _ _ _ _ Grp} : rename.
Arguments grp_right_id {_ _ _ _ _ Grp} : rename.
Arguments grp_left_inv {_ _ _ _ _ Grp} : rename.
Arguments grp_right_inv {_ _ _ _ _ Grp} : rename.
Arguments grp_op_proper {_ _ _ _ _ Grp} : rename.
Arguments grp_inv_proper {_ _ _ _ _ Grp} : rename.

(* Basic group properties *)
Section GroupProperties.
  Context `{Group G}.

  Lemma grp_inv_involutive (x: G): -(-x) ≡ x.
  Proof with auto.
    rewrite <-(grp_left_id x) at 2;
     rewrite <-grp_left_inv, <-grp_assoc, grp_left_inv, grp_right_id...
  Qed.

  Corollary grp_inv_neutral: -ɛ ≡@{G} ɛ.
  Proof with auto.
    rewrite <-grp_left_inv at 1; rewrite grp_right_id, grp_inv_involutive...
  Qed.

  Corollary grp_inv_inj (x y: G): x ≡ y → (-x) ≡ (-y).
  Proof. apply grp_inv_proper. Qed.

  Lemma perm_op_inv (x y: G) : -x - y ≡ -(y + x).
  Proof. Admitted.
End GroupProperties.