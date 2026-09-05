module

public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Mathlib.RingTheory.LaurentSeries
public import P2M.Util
public import P2M.Sol.S_ModularForm_exists_qExpansion_eq_aeval_mul_pow_levelOne

@[expose] public section

open UpperHalfPlane
open scoped MatrixGroups
theorem ModularForm.exists_qExpansion_eq_aeval_mul_pow_levelOne (N : ℕ) (F : ModularForm 𝒮ℒ (12 * (N : ℤ))) : ∃ P : Polynomial ℂ, P.natDegree ≤ N ∧ ((qExpansion 1 (F : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) P * ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ N := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_qExpansion_eq_aeval_mul_pow_levelOne.solution
