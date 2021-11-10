From stdpp Require Export list.
From Nominal Require Export Atom Group.

(* Permutation is just a list of pair of names. *)
Notation perm := (list (name * name)).
Notation "⟨ a , b ⟩" := (@cons (name * name) (a,b) nil).

(* Swap action on pair *)
Definition swap '(a,b) : name → name :=
  λ c, if decide (a = c) then b else if decide (b = c) then a else c.

(* Swap on perm *)
Definition swap_perm (p: perm): name → name := 
  λ a, foldl (λ x y, swap y x) a p.

(* List of names from perm *)
Fixpoint perm_dom (p: perm): nameset :=  
  match p with
  | [] => ∅
  | (a,b) :: p' => {[a; b]} ∪ perm_dom p'
  end.

Transparent listset_empty.
Lemma perm_dom_concat p: ∀ p', perm_dom (p ++ p') = (perm_dom p) ∪ (perm_dom p').
Proof.
  induction p.
  - intros; simpl; unfold empty, listset_empty, union, listset_union; simpl;
      destruct (perm_dom p'); reflexivity.
  - intros; simpl; destruct a as [a b]; rewrite IHp, assoc; auto.
    unfold Assoc, union, listset_union; intros [] [] []; rewrite assoc; [auto | typeclasses eauto].
Qed.
Opaque listset_empty.

Section SwapProperties.
  Context (a b c d : name) (p : name * name) (r s : perm).

  Lemma swap_left : swap (a,b) a = b.
  Proof. simpl; repeat case_decide; congruence. Qed.

  Lemma swap_right : swap (a,b) b = a.
  Proof. simpl; repeat case_decide; congruence. Qed.

  Lemma swap_neither1 : a ≠ c → b ≠ c → swap (a, b) c = c.
  Proof. intros; simpl; repeat case_decide; congruence. Qed.

  Lemma swap_neither2 : swap (a, b) c = c → (a ≠ c ∧ b ≠ c) ∨ (a = c ∧ b = c).
  Proof. 
    intros; simpl in *; try repeat case_decide; subst.
    - right; auto.
    - congruence.
    - left; auto.  
  Qed.

  Lemma swap_neq: a ≠ b → swap (c, d) a ≠ swap (c, d) b.
  Proof. intros; simpl; repeat case_decide; congruence. Qed.

  Lemma swap_id : swap (a,a) c = c.
  Proof. simpl; case_decide; congruence. Qed.

  Lemma swap_involutive : swap p (swap p a) = a.
  Proof. destruct p; simpl; repeat case_decide; congruence. Qed.

  Lemma swap_perm_app : swap_perm (r ++ s) a = swap_perm s (swap_perm r a).
  Proof. unfold swap_perm; rewrite foldl_app; simpl; auto. Qed.
End SwapProperties.

Lemma swap_perm_left_rev (p : perm) : ∀ a, swap_perm (reverse p) (swap_perm p a) = a.
Proof with auto.
  assert (HH: ∀ {A} (x: A) y, x :: y = [x] ++ y)... induction p; intros.
  - simpl...
  - rewrite HH, reverse_app, reverse_singleton, <-swap_perm_app, <-app_assoc,
      3?swap_perm_app; simpl; rewrite IHp; apply swap_involutive.
Qed.

Lemma swap_perm_right_rev (p : perm) a: swap_perm p (swap_perm (reverse p) a) = a.
Proof with auto.
  assert (HH: ∀ {A} (x: A) y, x :: y = [x] ++ y)... induction p.
  - simpl...
  - rewrite HH, reverse_app, reverse_singleton, <- swap_perm_app, <-app_assoc, 
      3?swap_perm_app; simpl; rewrite swap_involutive...
Qed.

Lemma swap_perm_neither (a b c: name): a ≠ b → a ≠ c → swap_perm ⟨b,c⟩ a = a.
Proof. unfold swap_perm, foldl; intros; rewrite swap_neither1; intuition. Qed.

Lemma swap_perm_left (a b: name): swap_perm ⟨a,b⟩ a = b.
Proof. unfold swap_perm, foldl; apply swap_left. Qed.

Lemma swap_perm_right (a b: name): swap_perm ⟨b,a⟩ a = b.
Proof. unfold swap_perm, foldl. apply swap_right. Qed.

Lemma swap_perm_neq p: ∀ a b, a ≠ b → swap_perm p a ≠ swap_perm p b.
Proof.
  induction p as [|[] ? IHp].
  - auto.
  - intros; simpl; apply IHp,swap_neq; auto.
Qed.

Lemma perm_notin_domain_id (p: perm) (a: name): a ∉ (perm_dom p) → swap_perm p a = a.
Proof.
  intros; induction p as [| [b c] p'].
  - reflexivity.
  - assert (HH: ∀ A (x: A) y, x :: y = [x] ++ y). { reflexivity. }
    rewrite HH, swap_perm_app; simpl in H; do 2 apply not_elem_of_union in H as [H ?];
    rewrite swap_perm_neither; set_solver.
Qed.

(** *Permutation as list forms a Group *)
#[global] Instance perm_neutral: Neutral perm := @nil (name * name).
#[global] Instance perm_operator: Operator perm := @app (name * name).
#[global] Instance perm_inverse: Inverse perm := @reverse (name * name).
#[global] Instance perm_equiv: Equiv perm :=
  λ p q: perm, ∀ a: name, swap_perm p a = swap_perm q a.
#[global] Instance perm_equivalence: Equivalence (≡@{perm}).
Proof. repeat split; repeat intro; [symmetry | etransitivity]; eauto. Qed.

#[global] Instance PermGrp: Group perm.
Proof with auto.
  split; unfold op, perm_operator, neutral, perm_neutral, inv, perm_inverse,
         equiv, perm_equiv in *; repeat intro...
  - typeclasses eauto.
  - rewrite 2?swap_perm_app; do 2 match goal with H : context[_ = _] |- _ => rewrite H end...
  - transitivity (swap_perm (reverse y) (swap_perm x (swap_perm (reverse x) a)));
    [rewrite H, swap_perm_left_rev | rewrite swap_perm_right_rev]...
  - rewrite app_assoc...
  - rewrite app_nil_r...
  - rewrite swap_perm_app, swap_perm_right_rev...
  - rewrite swap_perm_app, swap_perm_left_rev...
Qed.

Section PermGroupProperties.
  Context (a b c : name).

  Lemma perm_equiv_neutral: ⟨a,a⟩ ≡ ɛ@{perm}.
  Proof. unfold equiv, perm_equiv, swap_perm; intros; simpl; case_decide; auto. Qed.

  Lemma perm_expand :
    c ≠ a -> c ≠ b -> ⟨a,c⟩ ≡@{perm} ⟨a,b⟩ + ⟨b,c⟩ + ⟨a,b⟩.
  Proof.
    intros; unfold equiv, perm_equiv, swap_perm; intros; simpl; 
      repeat case_decide; subst; congruence.
  Qed.

  Lemma perm_swap : ⟨a,b⟩ ≡ ⟨b,a⟩.
  Proof. 
    unfold equiv, perm_equiv, swap_perm; intros; simpl; 
      repeat case_decide; subst; auto.
  Qed.

  Lemma perm_duplicate: ⟨a,b⟩ + ⟨a,b⟩ ≡ ɛ@{perm}.
  Proof.
    unfold equiv, perm_equiv, swap_perm; intros; simpl;
      repeat case_decide; subst; first [congruence | auto].
  Qed.
End PermGroupProperties.

Lemma perm_inv a b: ⟨a,b⟩ ≡ -⟨a,b⟩.
Proof. Admitted.

Lemma perm_comm_distr a b p: ⟨a,b⟩ + p ≡ p + ⟨swap_perm p a, swap_perm p b⟩.
Proof.
  unfold equiv, perm_equiv, op, perm_operator; intros x;
  destruct (decide (a = x)), (decide (b = x)); subst; rewrite 2!swap_perm_app.
  - rewrite 2!perm_equiv_neutral; auto.
  - rewrite 2!swap_perm_left; auto.
  - rewrite 2!swap_perm_right; auto. 
  - rewrite 2!swap_perm_neither; try apply swap_perm_neq; intuition.
Qed.

Lemma perm_notin_dom_comm a b p: a ∉ perm_dom p → b ∉ perm_dom p → ⟨a,b⟩ + p ≡ p + ⟨a,b⟩.
Proof.
  intros; rewrite perm_comm_distr; unfold equiv, perm_equiv; intros x;
    rewrite 2!(perm_notin_domain_id p); auto.
Qed.

Lemma perm_dom_inv p a: a ∉ perm_dom p → a ∉ perm_dom (-p).
Proof. 
  induction p as [| p p' IHp]; intros H.
  - simpl in *; auto.
  - assert (HH: ∀ A (x: A) y, x :: y = [x] ++ y). { intros; simpl; auto. }
    unfold inv, perm_inverse; rewrite reverse_cons; rewrite HH in H.
    rewrite perm_dom_concat in *; set_solver.
Qed.

(* Group Action  *)
Class PermAction X := action: perm → X → X.
#[global] Hint Mode PermAction ! : typeclass_instances.

(* CAUSA PROBLEMAS COM REESCRITA ENVOLVENDO action (- p)
  Instance: Params (@action) 2 := {}. *)

Infix "∙" := action (at level 60, right associativity): nominal_scope.
Notation "(∙)" := action (only parsing): nominal_scope.
Notation "(∙ x )" := (action x) (only parsing): nominal_scope.
Notation "( x ∙)" := (λ y, action y x) (only parsing): nominal_scope.

(* Permutation type is a type with a permutation group (left) action *)
Class Perm (X : Type) `{Act: PermAction X, Equiv X}: Prop := {
  gact_setoid :> Equivalence(≡@{X});
  gact_proper :> Proper ((≡@{perm}) ⟹ (≡@{X}) ⟹ (≡@{X})) (∙);

  gact_id: ∀ (x: X), ɛ@{perm} ∙ x ≡@{X} x;
  gact_compat: ∀ (p q: perm) (x: X), p ∙ (q ∙ x) ≡@{X} (q + p) ∙ x
}.
#[global] Hint Mode Perm ! - - : typeclass_instances.

Existing Instance gact_setoid.
Existing Instance gact_proper.

(* Arguments gact_id {_ _ _ _ _ Grp _ _ _ GAct} : rename.
Arguments gact_compat {_ _ _ _ _ Grp _ _ _ GAct} : rename.
Arguments gact_proper {_ _ _ _ _ Grp _ _ _ GAct} : rename. *)

Section GroupActionProperties.
  Context `{Perm X}.

  Corollary perm_left_inv (x: X) p: (-p) ∙ p ∙ x ≡ x.
  Proof. rewrite gact_compat, grp_right_inv, gact_id; auto. Qed.

  Corollary perm_rigth_inv (x: X) p: p ∙ (-p) ∙ x ≡ x.
  Proof. rewrite gact_compat, grp_left_inv, gact_id; auto. Qed.

  Lemma perm_iff (x y: X) p: p ∙ x ≡ y ↔ x ≡ (-p) ∙ y.
  Proof. split; intros A; 
    [rewrite <-A, perm_left_inv | rewrite A, perm_rigth_inv]; auto.
  Qed.

  Lemma perm_inj (x y: X) p: p ∙ x ≡ p ∙ y ↔ x ≡ y.
  Proof. split; intros A; 
    [apply perm_iff in A; rewrite <-(perm_left_inv y p) | rewrite A]; auto.
  Qed.

  Lemma perm_inv_empty_act (x: X): (-ɛ) ∙ x ≡ x.
  Proof. rewrite grp_inv_neutral; apply gact_id. Qed.
End GroupActionProperties.

(* #[global] Instance action_perm_proper `{Perm A}: Proper ((≡@{perm}) ⟹ (≡@{A}) ⟹ (≡@{A})) action.
Proof. apply gact_proper. Qed. *)

Section PermProperties.
  Context `{Perm X} (a b c: name) (x: X).

  Lemma perm_action_duplicate: ⟨a,b⟩ ∙ ⟨a,b⟩ ∙ x ≡ x.
  Proof. rewrite gact_compat, perm_duplicate; apply gact_id. Qed.

  Lemma perm_action_equal: ⟨a,a⟩ ∙ x ≡ x.
  Proof. rewrite perm_equiv_neutral; apply gact_id. Qed.

  Lemma perm_comm p: a ∉ perm_dom p → b ∉ perm_dom p → ⟨a,b⟩ ∙ p ∙ x ≡ p ∙ ⟨a,b⟩ ∙ x.
  Proof. intros; rewrite gact_compat, <-perm_notin_dom_comm, <-gact_compat; auto. Qed.

End PermProperties.