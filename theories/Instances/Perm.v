(* Perm forms a nominal set *)
From Nominal Require Import Permutation Nominal.

#[export] Instance perm_action: PermAction Perm :=
    fun p' p => (-p') + (p + p').

#[export] Instance perm_support: Support Perm := perm_dom.

#[export] Instance perm_permt: PermT Perm.
Proof. Admitted.

#[export] Instance perm_nominal: Nominal Perm.
Proof. Admitted.

Lemma perm_distr w z (p q: Perm): ⟨w,z⟩ • (p + q) ≡ (⟨w,z⟩ • p) + (⟨w,z⟩ • q).
Proof. 
  unfold action, perm_action; rewrite <-perm_inv, !grp_assoc. 
  assert (HH: ⟨ w, z ⟩ + p + ⟨ w, z ⟩ + ⟨ w, z ⟩ + q + ⟨ w, z ⟩ ≡ ⟨ w, z ⟩ + p + (⟨ w, z ⟩ + ⟨ w, z ⟩) + q + ⟨ w, z ⟩).
  { rewrite !grp_assoc; reflexivity. }
  rewrite HH; clear HH.
  rewrite perm_duplicate.
  assert (HH: ⟨ w, z ⟩ + p + ɛ + q + ⟨ w, z ⟩ ≡ ⟨ w, z ⟩ + p + (ɛ + (q + ⟨ w, z ⟩))).
  { rewrite !grp_assoc; reflexivity. } rewrite HH; clear HH.
  rewrite grp_left_id, !grp_assoc; reflexivity.
Qed.