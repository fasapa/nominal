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
(* Notation "( +@{ A } )" := (@op A _) (only parsing) : nominal_scope. *)
Notation "(+ x )" := (op x) (only parsing) : nominal_scope.
Notation "( x +)" := (λ y, op y x) (only parsing) : nominal_scope.

Class Inverse A := inv : A → A.
#[global] Hint Mode Inverse ! : typeclass_instances.
Instance: Params (@inv) 1 := {}.

Notation "- x" := (inv x) : nominal_scope.
Notation "(-)" := inv (only parsing) : nominal_scope.
(* Notation "( -@{ A } )" := (@inv A _) (only parsing) : nominal_scope. *)
Notation "x - y" := (x + (-y))%nom : nominal_scope.

Section GroupDef.
  Context (A : Type) `{Ntr: Neutral A, Opr: Operator A, Inv: Inverse A, EqG: Equiv A}.

  Class Group: Prop := {
    group_setoid :> Equivalence(≡@{A});
    group_op_proper :> Proper ((≡@{A}) ==> (≡@{A}) ==> (≡@{A})) (+);
    group_inv_proper :> Proper ((≡@{A}) ==> (≡@{A})) (-);

    group_assoc : ∀ x y z, x + (y + z) ≡@{A} (x + y) + z;

    group_left_id : ∀ x, ɛ + x ≡@{A} x;
    group_right_id : ∀ x, x + ɛ ≡@{A} x;

    group_left_inv : ∀ x, (-x) + x ≡@{A} ɛ;
    group_right_inv : ∀ x, x - x ≡@{A} ɛ;
  }.
End GroupDef.
Print Group.
(* #[global] Hint Mode Group ! - - - -: typeclass_instances. *)

Arguments group_assoc {_ _ _ _ _ Grp} : rename.
Arguments group_left_id {_ _ _ _ _ Grp} : rename.
Arguments group_right_id {_ _ _ _ _ Grp} : rename.
Arguments group_left_inv {_ _ _ _ _ Grp} : rename.
Arguments group_right_inv {_ _ _ _ _ Grp} : rename.
Arguments group_op_proper {_ _ _ _ _ Grp} : rename.
Arguments group_inv_proper {_ _ _ _ _ Grp} : rename.

(* Basic group theory properties *)
Section GroupProperties.
  Context `{Group G}.

  Corollary group_inv_involutive (x: G): --x ≡ x.
  Proof with auto.
    rewrite <-(group_left_id x) at 2;
     rewrite <-group_left_inv, <-group_assoc, group_left_inv, group_right_id...
  Qed.

  Corollary inv_neutral: -ɛ ≡@{G} ɛ.
  Proof with auto.
    rewrite <-group_left_inv at 1; rewrite group_right_id, group_inv_involutive...
  Qed.

  Corollary group_inv_inj (x y: G): x ≡ y → (-x) ≡ (-y).
  Proof. apply group_inv_proper. Qed.
End GroupProperties.

(* Group Action  *)
(* Class Action `{Grp: Group A} A X := action: A -> X -> X. *)
Class Action A X := action: A -> X -> X.
#[global] Hint Mode Action ! ! : typeclass_instances.
(* CAUSA PROBLEMAS COM REESCRITA ENVOLVENDO action (- p)
  Instance: Params (@action) 2 := {}. *)

Infix "•" := action (at level 60, right associativity) : nominal_scope.
Notation "(•)" := action (only parsing) : nominal_scope.
(* Notation "( •@{ A X } )" := (@action A X _) (only parsing) : nominal_scope. *)
Notation "(• x )" := (action x) (only parsing) : nominal_scope.
Notation "( x •)" := (λ y, action y x) (only parsing): nominal_scope.

Section GroupAction.
  Context (A X: Type) `{Grp: Group A, Act : Action A X, Equiv X}.

  Class GAction : Prop := {
    gact_group :> Group A;
    gact_setoid :> Equivalence(≡@{X});
    gact_proper :> Proper ((≡@{A}) ==> (≡@{X}) ==> (≡@{X})) (•);

    gact_id : ∀ (x: X), ɛ@{A} • x ≡@{X} x;
    gact_compat: ∀ (p q: A) (x: X), p • (q • x) ≡@{X} (q + p) • x
  }.
End GroupAction.

Arguments gact_compat {_ _ _ _ _ _ _ EqX GAct} : rename.
Arguments gact_id {_ _ _ _ _ _ _ EqX GAct} : rename.
Arguments gact_proper {_ _ _ _ _ _ _ EqX GAct} : rename.

Section GroupActionProperties.
  Context `{GAction G X}.

  Corollary perm_left_inv (x: X) (p : G): (-p) • p • x ≡ x.
  Proof. rewrite gact_compat, group_right_inv, gact_id; auto. Qed.

  Corollary perm_rigth_inv (x: X) (p : G): p • (-p) • x ≡ x.
  Proof. rewrite gact_compat, group_left_inv, gact_id; auto. Qed.

  Lemma perm_iff (x y: X) (p : G): p • x ≡ y <-> x ≡ (-p) • y.
  Proof.
    split; intros A;
      [rewrite <-A, perm_left_inv | rewrite A, perm_rigth_inv]; auto.
  Qed.

  Lemma perm_inj (x y: X) (p : G): p • x ≡ p • y <-> x ≡ y.
  Proof.
    split; intros A; [apply perm_iff in A; rewrite <-(perm_left_inv y p) | rewrite A]; auto.
  Qed.
End GroupActionProperties.
