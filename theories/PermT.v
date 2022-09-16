From Nominal Require Export Group Swap Permutation.

(* Permutation Type *)
Class PermAction X := action: Perm → X → X.
#[export] Hint Mode PermAction ! : typeclass_instances.

(* CAUSA PROBLEMAS COM REESCRITA ENVOLVENDO action (- p)
  Instance: Params (@action) 2 := {}. *)

Infix "•" := action (at level 60, right associativity): nominal_scope.
Notation "(•)" := action (only parsing): nominal_scope.
Notation "(• x )" := (action x) (only parsing): nominal_scope.
Notation "( x •)" := (λ y, action y x) (only parsing): nominal_scope.

(* Permutation type is a type with a permutation group (left) action *)
Class PermT (X : Type) `{Act: PermAction X, Equiv X}: Prop := {
  gact_setoid :> Equivalence(≡@{X});
  gact_proper :> Proper ((≡@{Perm}) ==> (≡@{X}) ==> (≡@{X})) (•);

  gact_id: ∀ (x: X), ɛ • x ≡@{X} x;
  gact_compat: ∀ (p q: Perm) (x: X), p • (q • x) ≡@{X} (q + p) • x
}.

#[export] Hint Mode PermT ! - - : typeclass_instances.
#[export] Existing Instance gact_setoid.
#[export] Existing Instance gact_proper.

(* Arguments gact_id {_ _ _ _ _ Grp _ _ _ GAct} : rename.
Arguments gact_compat {_ _ _ _ _ Grp _ _ _ GAct} : rename.
Arguments gact_proper {_ _ _ _ _ Grp _ _ _ GAct} : rename. *)

Section PermTypeProperties.
  Context `{PermT X}.

  Corollary perm_left_inv (x: X) p: (-p) • p • x ≡ x.
  Proof. rewrite gact_compat, grp_right_inv, gact_id; auto. Qed.

  Corollary perm_rigth_inv (x: X) p: p • (-p) • x ≡ x.
  Proof. rewrite gact_compat, grp_left_inv, gact_id; auto. Qed.

  Lemma perm_iff (x y: X) p: p • x ≡ y ↔ x ≡ (-p) • y.
  Proof. split; intros A; 
    [rewrite <-A, perm_left_inv | rewrite A, perm_rigth_inv]; auto.
  Qed.

  Lemma perm_inj (x y: X) p: p • x ≡ p • y ↔ x ≡ y.
  Proof. split; intros A; 
    [apply perm_iff in A; rewrite <-(perm_left_inv y p) | rewrite A]; auto.
  Qed.

  Lemma perm_inv_empty_act (x: X): (-ɛ) • x ≡ x.
  Proof. rewrite grp_inv_neutral; apply gact_id. Qed.

  Lemma perm_action_duplicate a b (x: X): ⟨a,b⟩ • ⟨a,b⟩ • x ≡ x.
  Proof. rewrite gact_compat, perm_duplicate; apply gact_id. Qed.

  Lemma perm_action_equal a (x: X): ⟨a,a⟩ • x ≡ x.
  Proof. rewrite perm_equiv_neutral; apply gact_id. Qed.

  Lemma perm_comm a b p (x: X): a ∉ perm_dom p → b ∉ perm_dom p → ⟨a,b⟩ • p • x ≡ p • ⟨a,b⟩ • x.
  Proof. intros; rewrite gact_compat, <-perm_notin_dom_comm, <-gact_compat; auto. Qed.

  Lemma perm_swap_distr a b p (x: X): p • ⟨a,b⟩ • x ≡ ⟨perm_swap p a, perm_swap p b⟩ • p • x.
  Proof. rewrite 2gact_compat, perm_comm_distr; auto. Qed.
End PermTypeProperties.

(* #[global] Instance action_perm_proper `{Perm A}: Proper ((≡@{perm}) ⟹ (≡@{A}) ⟹ (≡@{A})) action.
Proof. apply gact_proper. Qed. *)