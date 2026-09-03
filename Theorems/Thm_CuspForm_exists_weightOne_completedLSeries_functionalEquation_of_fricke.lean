import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_exists_weightOne_completedLSeries_functionalEquation_of_fricke

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_weightOne_completedLSeries_functionalEquation_of_fricke
    (M : ℕ) [NeZero M] (g g' : CuspForm (Gamma1 M) 1) (c : ℂ) (hc : c ≠ 0)
    (hW : ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 →
        g τ' = c * (τ : ℂ) * g' τ) :
    ∃ (Λ Λ' : ℂ → ℂ) (σ₁ : ℝ), Differentiable ℂ Λ ∧ Differentiable ℂ Λ' ∧
      (∀ s : ℂ, σ₁ < s.re →
        LSeriesSummable (fun n => ModularFormClass.qCoeff g n) s ∧
        LSeriesSummable (fun n => ModularFormClass.qCoeff g' n) s ∧
        Λ s = ((Real.sqrt M / (2 * Real.pi) : ℝ) : ℂ) ^ s * Complex.Gamma s *
                LSeries (fun n => ModularFormClass.qCoeff g n) s ∧
        Λ' s = ((Real.sqrt M / (2 * Real.pi) : ℝ) : ℂ) ^ s * Complex.Gamma s *
                LSeries (fun n => ModularFormClass.qCoeff g' n) s) ∧
      ∀ s : ℂ, Λ s = c * Complex.I / (Real.sqrt M : ℂ) * Λ' (1 - s) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_weightOne_completedLSeries_functionalEquation_of_fricke.solution
