(* Perm forms a nominal set *)
From Nominal Require Import Permutation Fresh Nominal Instances.Name.

#[export] Instance PermActionPerm: PermAction Perm :=
    fun p' p => (-p') + (p + p').

#[export] Instance PermSupport: Support Perm := perm_dom.

Lemma lala (a b: Perm) : a ≡ b → -a ≡ -b.
Proof. intros H. rewrite H. reflexivity. Qed.

#[export] Instance PermPermT: PermT Perm.
Proof. split.
    - typeclasses eauto.
    - unfold action, PermActionPerm. repeat intro. 
      unfold "+", perm_operator. repeat rewrite perm_swap_app.
      rewrite H; f_equal. rewrite H0; f_equal. apply lala; assumption.
    - unfold action, PermActionPerm. repeat intro. f_equal.
      unfold "+", perm_operator; simpl. apply app_nil_r.
    - repeat intro. unfold action,PermActionPerm. unfold "+",perm_operator. f_equal.
      unfold "- _", perm_inverse. rewrite reverse_app. rewrite !app_assoc. reflexivity.
Qed.

#[export] Instance PermNominal: Nominal Perm.
Proof. split.
  - apply PermPermT.
  - intros x a b Ha Hb. unfold action, PermActionPerm.
    rewrite <-(perm_inv a b), !grp_assoc. rewrite perm_notin_dom_comm.
    + rewrite <-grp_assoc, perm_duplicate, grp_right_id. reflexivity.
    + assumption.
    + assumption.
Qed.

Lemma perm_distr w z (p q: Perm): ⟨w,z⟩ • (p + q) ≡ (⟨w,z⟩ • p) + (⟨w,z⟩ • q).
Proof. 
  unfold action,PermActionPerm; rewrite <-perm_inv, !grp_assoc. 
  assert (HH: ⟨w,z⟩ + p + ⟨w,z⟩ + ⟨w,z⟩ + q + ⟨w,z⟩ ≡ ⟨w,z⟩ + p + (⟨w,z⟩ + ⟨w,z⟩) + q + ⟨w,z⟩).
  { rewrite !grp_assoc; reflexivity. }
  rewrite HH; clear HH.
  rewrite perm_duplicate.
  assert (HH: ⟨w,z⟩ + p + ɛ + q + ⟨w,z⟩ ≡ ⟨w, z⟩ + p + (ɛ + (q + ⟨w,z⟩))).
  { rewrite !grp_assoc; reflexivity. } rewrite HH; clear HH.
  rewrite grp_left_id, !grp_assoc; reflexivity.
Qed.

Lemma perm_distr_1 (a b w z: Name) (p: Perm):
  w ≠ a → w ≠ b → z ≠ a → z ≠ b →
  ⟨a,b⟩ + (⟨w,z⟩•p) ≡ (⟨w, z⟩•⟨a,b⟩) + (⟨w,z⟩•p).
Proof.
  intros; rewrite <-(fresh_fixpoint w z (⟨ a, b ⟩)) at 1; auto;
  apply support_fresh; set_solver.
Qed.

Lemma perm_distr_2 (a b w z: Name) (p: Perm):
  (⟨w,z⟩•⟨a,b⟩) + (⟨w,z⟩•p) ≡ ⟨w,z⟩•(⟨a,b⟩ + p).
Proof. symmetry; apply perm_distr. Qed.

Lemma perm_distr_3 (a b w z: Name) (p: Perm):
  w ∉ perm_dom p → z ∉ perm_dom p → w ≠ a → z ≠ a →
  ⟨w,z⟩•⟨a,b⟩+p ≡ ⟨a,⟨w,z⟩•b⟩+p.
Proof.
  intros. rewrite perm_distr, (support_spec p w z); [| set_solver | set_solver];
  unfold action at 1; unfold PermActionPerm; 
  rewrite perm_comm_distr,perm_swap_neither; [| set_solver | set_solver].
  rewrite !grp_assoc,grp_left_inv,grp_left_id; reflexivity.
Qed.

Lemma notin_support_comp_perm (a: Name) (p q : Perm): a ∉ support (p + q) ↔ a ∉ support p ∧ a ∉ support q.
Proof.
  split.
  - intros H1; unfold support,PermSupport,op,perm_operator in H1; rewrite perm_dom_concat in H1.
    apply not_elem_of_union in H1; auto.
  - intros H1; unfold support,PermSupport,op,perm_operator; rewrite perm_dom_concat;
    apply not_elem_of_union; assumption.
Qed.

Lemma notin_support_comp_swap (c a b: Name) : c ∉ support ⟨a,b⟩ ↔ c ∉ support a ∧ c ∉ support b.
Proof.
  split.
  - intros H1; unfold support in H1; simpl in H1; split; set_solver.
  - intros []; unfold support; simpl. set_solver.
Qed.

Lemma support_empty: support ɛ@{Perm} ≡ ∅.
Proof. unfold support; simpl; reflexivity. Qed.