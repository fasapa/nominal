(* Perm forms a nominal set *)
From Nominal Require Import Permutation Fresh Nominal Instances.Name.

#[export] Instance PermActionPerm: PermAction Perm :=
    fun p' p => (-p') + (p + p').

#[export] Instance PermSupport: Support Perm := perm_dom.

#[export] Instance PermPermT: PermT Perm.
Proof. Admitted.

#[export] Instance PermNominal: Nominal Perm.
Proof. Admitted.

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