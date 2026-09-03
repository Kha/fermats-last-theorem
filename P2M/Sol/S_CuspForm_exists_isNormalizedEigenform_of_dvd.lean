import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_level_mul
import P2M.Util
namespace P2MW.S_CuspForm_exists_isNormalizedEigenform_of_dvd
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularFormClass

theorem solution {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf : f.IsNormalizedEigenform) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2, g.IsNormalizedEigenform ∧
      ∀ n : ℕ, n.Coprime N → qCoeff g n = qCoeff f n := by

  have key : ∀ (t M : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2), M * t ≠ 0 →
      f.IsNormalizedEigenform →
      ∃ g : CuspForm (CongruenceSubgroup.Gamma0 (M * t)) 2, g.IsNormalizedEigenform ∧
        ∀ n : ℕ, n.Coprime t → qCoeff g n = qCoeff f n := by
    intro t
    induction t using Nat.recOnMul with
    | zero => intro M f h; simp at h
    | one => intro M f _ hf; rw [Nat.mul_one]; exact ⟨f, hf, fun n _ ↦ rfl⟩
    | prime p hp =>
      intro M f hM hf
      haveI : NeZero M := ⟨fun h ↦ hM (by rw [h, Nat.zero_mul])⟩
      obtain ⟨g, hg, hq⟩ := CuspForm.exists_isNormalizedEigenform_level_mul f hf hp
      exact ⟨g, hg, fun n hn ↦ hq n fun h ↦ hp.one_lt.ne'
        (Nat.Coprime.eq_one_of_dvd (Nat.coprime_comm.mp hn) h)⟩
    | mul a b iha ihb =>
      intro M f hM hf
      have hMa : M * a ≠ 0 := fun h ↦ hM (by rw [← Nat.mul_assoc, h, Nat.zero_mul])
      obtain ⟨g₁, hg₁, hq₁⟩ := iha M f hMa hf
      obtain ⟨g₂, hg₂, hq₂⟩ := ihb (M * a) g₁ (by rwa [Nat.mul_assoc]) hg₁
      rw [← Nat.mul_assoc]
      exact ⟨g₂, hg₂, fun n hn ↦ (hq₂ n (Nat.Coprime.coprime_mul_left_right hn)).trans
        (hq₁ n (Nat.Coprime.coprime_mul_right_right hn))⟩
  obtain ⟨t, rfl⟩ := hMN
  obtain ⟨g, hg, hq⟩ := key t M f (NeZero.ne _) hf
  exact ⟨g, hg, fun n hn ↦ hq n (Nat.Coprime.coprime_mul_left_right hn)⟩
