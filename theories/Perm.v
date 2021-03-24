From stdpp Require Import list.
From Nominal Require Export Name Group.

Notation perm := (list (name * name)).

Definition swap '(a,b) : name -> name :=
  λ c, if decide (a = c) then b else if decide (b = c) then a else c.

Definition perm_action (p: perm): name -> name :=
  λ a, foldr swap a p.

(* Swap & perm properties *)
Lemma swap_id (a x: name): swap (a,a) x = x.
Proof. simpl; case_decide; congruence. Qed.

Lemma swap_involutive a x: swap a (swap a x) = x.
Proof. destruct a; simpl; repeat case_decide; congruence. Qed.

Lemma perm_action_app p q x: perm_action (p ++ q) x = perm_action p (perm_action q x).
Proof. unfold perm_action; rewrite foldr_app; auto. Qed.

Lemma perm_action_left_rev p x: perm_action (reverse p) (perm_action p x) = x.
Proof with auto.
  induction p.
  - simpl...
  - assert (HH1: ∀ a, a :: p = [a] ++ p)...
    rewrite HH1, reverse_app, reverse_singleton, <-perm_action_app, <-app_assoc, 3?perm_action_app;
      simpl; rewrite swap_involutive...
Qed.

Lemma perm_action_right_rev p: forall x, perm_action p (perm_action (reverse p) x) = x.
Proof with auto.
  induction p; intros.
  - simpl...
  - assert (HH1: ∀ a, a :: p = [a] ++ p)...
    rewrite HH1, reverse_app, reverse_singleton, <-perm_action_app, <-app_assoc, 3?perm_action_app,
    IHp; simpl; apply swap_involutive.
Qed.

(** *Permutation group  *)
Instance perm_neutral: Neutral perm := @nil (name * name).
Instance perm_operator: Operator perm := @app (name * name).
Instance perm_inverse: Inverse perm := @reverse (name * name).
Instance perm_equiv: Equiv perm := λ p q: perm, ∀ a: name, perm_action p a = perm_action q a.
Instance perm_equivalence: Equivalence (≡@{perm}).
Proof. repeat split; repeat intro; [symmetry | etransitivity]; eauto. Qed.

Instance perm_group: Group perm.
Proof with auto.
  split; unfold op, perm_operator, neutral, perm_neutral, inv, perm_inverse,
         equiv, perm_equiv in *; repeat intro...
  - rewrite app_assoc...
  - rewrite app_nil_r...
  - rewrite perm_action_app, perm_action_left_rev...
  - rewrite perm_action_app, perm_action_right_rev...
  - typeclasses eauto.
  - rewrite 2?perm_action_app; do 2 match goal with H : context[_ = _] |- _ => rewrite H end...
  - transitivity (perm_action (reverse y) (perm_action x (perm_action (reverse x) a)));
      [rewrite H, perm_action_left_rev | rewrite perm_action_right_rev]...
Qed.

(** *Permtutation Types *)
Class PermAction X := action_perm :> Action perm_group X.
Class Perm X `{XA: PermAction X, Equiv X} : Prop :=
  perm_type :> @GroupAction perm X _ _ _ _ perm_group (@action_perm X XA) _.

(* Permutation types properties *)
Section PermTypeProperties.
  Context `{Perm X}.

  Lemma perm_left_inv (x: X) p: (-p) ∙ p ∙ x ≡ x.
  Proof. rewrite action_compat, group_right_inv, action_id; auto. Qed.

  Lemma perm_rigth_inv (x: X) p: p ∙ (-p) ∙ x ≡ x.
  Proof. rewrite action_compat, group_left_inv, action_id; auto. Qed.

  Lemma perm_iff (x y: X) p: p ∙ x ≡ y <-> x ≡ (-p) ∙ y.
  Proof.
    split; intros A; [rewrite <-A, perm_left_inv | rewrite A, perm_rigth_inv]; auto.
  Qed.

  Lemma perm_inj (x y: X) p: p ∙ x ≡ p ∙ y <-> x ≡ y.
  Proof.
    split; intros A; [apply perm_iff in A; rewrite <-(perm_left_inv y p) | rewrite A]; auto.
  Qed.

  Lemma swap_equiv_neutral a: [(a,a)] ≡ ε.
  Proof. unfold equiv, perm_equiv, perm_action; intros; simpl; case_decide; auto. Qed.

  Lemma swap_expand (a c b: name):
    c ≠ a -> c ≠ b -> [(a,c)] ≡@{perm} [(a,b)] + [(b,c)] + [(a,b)].
  Proof.
    intros; unfold equiv, perm_equiv, perm_action; intros; simpl; repeat case_decide; subst; congruence.
  Qed.

End PermTypeProperties.

(* Definition fresh' `{Nominal X} (a: name) (x: X): Prop := *)
(*   exists c: name, c ∉ (support x) /\ [(a,c)] ∙ x ≡ x. *)


(* Proof. intros. Admitted. *)

(* Lemma fresh_support `{Nominal X} (x: X) a: a ∉ support x -> fresh' a x. *)
(* Proof. intros; exists a; split. *)
(*        - auto. *)
(*        - rewrite lolol. apply action_id. *)
(* Qed. *)

(* Lemma fresh11 `{Nominal X} (x: X): exists a, fresh' a x. *)
(* Proof. *)
(*   exists (fresh (support x)), (fresh (support x)); split. *)
(*   - apply is_fresh. *)
(*   - rewrite lolol; apply action_id. *)
(* Qed. *)

(* Theorem some_any `{Nominal X} (x: X) a: *)
(*   fresh' a x -> (forall c, c ∉ support x -> [(a,c)] ∙ x ≡ x). *)
(* Proof. *)
(*   intros Fa ? Sc; apply fresh_support in Fa as [b [HB HA]]. *)
(*   assert (HH: [(a,c)] ≡ ( [(a,b)] + [(b,c)] + [(a,b)] )). admit. *)
(*   rewrite HH. rewrite <-2!action_compat, HA. *)
(*   rewrite (support_spec _ _ b c); auto. *)
(* Admitted. *)

(*   destruct (decide (c = a)), (decide (c = b)); subst. *)
(*   - auto. *)
(*   - rewrite lolol; apply action_id. *)
(*   - auto. *)
(*   - assert (HH: [(a,c)] ≡ ( [(a,b)] + [(b,c)] + [(a,b)] )). admit. *)
(*     rewrite HH. rewrite <-2!action_compat, Hb. *)
(*     rewrite (support_spec _ _ b c); auto. *)
(* Admitted. *)
(*     destruct (c ≡a a), (c ≡a b); subst; auto. *)
(*   -                             (* c ≡ a /\ c ≢ b *) *)
(*     apply permt_id. *)
(*   -                             (* c ≢ a /\ c ≢ b *) *)
(*     rewrite (equiv1 _ b _); auto. repeat rewrite <- gct_compat. *)
(*     rewrite Hb. rewrite (supp_spec _ _ b c); auto. *)
(* Qed. *)
