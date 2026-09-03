import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Theorems.Thm_ModularForm_sturm_bound_of_isArithmetic
import Theorems.Thm_ModularForm_finiteDimensional_of_isArithmetic
import P2M.Util
namespace P2MW.S_ModularForm_finiteDimensional_and_finrank_le_of_isArithmetic

p2m_open "UpperHalfPlane ModularForm P2MW.S_ModularForm_finiteDimensional_and_finrank_le_of_isArithmetic.ModularForm SlashInvariantForm Matrix.SpecialLinearGroup ConjAct"
p2m_open_scoped "MatrixGroups ModularForm P2MW.S_ModularForm_finiteDimensional_and_finrank_le_of_isArithmetic.ModularForm Topology Manifold Pointwise"

noncomputable section

namespace ModularForm p2m_export "ModularForm" "ext sturm_bound_of_isArithmetic finiteDimensional_of_isArithmetic" end ModularForm
p2m_open_scoped "ModularForm" in

def ModularForm.qExpansionCoeffs_W2D {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.HasDetOne] (k : ℤ) {h : ℝ}
    (hh : 0 < h) (h𝒢 : h ∈ 𝒢.strictPeriods) (B : ℕ) : ModularForm 𝒢 k →ₗ[ℂ] (Fin B → ℂ) where
  toFun f n := (qExpansion h f).coeff n
  map_add' f g := by
    ext n
    simp [ModularForm.qExpansion_add hh h𝒢]
  map_smul' a f := by
    ext n
    simp [ModularForm.qExpansion_smul hh h𝒢]

p2m_open_scoped "ModularForm" in
lemma ModularForm.le_order_of_qExpansionCoeffs_eq_zero_W2D {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.HasDetOne]
    {k : ℤ} {h : ℝ} (hh : 0 < h) (h𝒢 : h ∈ 𝒢.strictPeriods) {B : ℕ} {f : ModularForm 𝒢 k}
    (hf : ModularForm.qExpansionCoeffs_W2D k hh h𝒢 B f = 0) : (B : ℕ∞) ≤ (qExpansion h f).order :=
  PowerSeries.nat_le_order _ _ fun n hn ↦ by have h__af := congr_fun hf ⟨n, hn⟩; simp at h__af; exact h__af

private theorem finrank_le_engine (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] [𝒢.HasDetOne] (k : ℤ) (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods) : Module.finrank ℂ (ModularForm 𝒢 k) ≤ (k * 𝒢.relIndex 𝒮ℒ).toNat / 12 + 1 := by
  set B := (k * 𝒢.relIndex 𝒮ℒ).toNat / 12 + 1 with hB
  have hinj : Function.Injective (ModularForm.qExpansionCoeffs_W2D k one_pos h1 B) := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    exact ModularForm.sturm_bound_of_isArithmetic h1 (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _)
      (ModularForm.le_order_of_qExpansionCoeffs_eq_zero_W2D _ h1 hf))
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

theorem solution (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] [𝒢.HasDetOne] (k : ℤ) (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods) :
    FiniteDimensional ℂ (ModularForm 𝒢 k) ∧
      Module.finrank ℂ (ModularForm 𝒢 k) ≤ (k * 𝒢.relIndex 𝒮ℒ).toNat / 12 + 1 :=
  ⟨ModularForm.finiteDimensional_of_isArithmetic 𝒢 k, finrank_le_engine 𝒢 k h1⟩

end
