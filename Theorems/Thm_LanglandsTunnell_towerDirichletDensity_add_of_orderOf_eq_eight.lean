import Definitions.Def_LanglandsTunnell_AnalyticGates
import Mathlib.RingTheory.Frobenius
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_towerDirichletDensity_add_of_orderOf_eq_eight
attribute [-instance] FrobeniusDensity.liesOver_ratBelow

open NumberField Ideal FrobeniusDensity Filter Topology Asymptotics

theorem LanglandsTunnell.towerDirichletDensity_add_of_orderOf_eq_eight
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    (σ : L ≃ₐ[ℚ] L) (h8 : orderOf σ = 8) (h3 : IsConj σ (σ ^ 3)) :
    (∀ s : ℝ, 1 < s → Summable (fun ℓ : ℕ => (classIndicator σ ℓ : ℝ) * (ℓ : ℝ) ^ (-s))) ∧
    (fun s : ℝ =>
        (∑' ℓ : ℕ, ((classIndicator σ ℓ : ℝ) + (classIndicator (σ ^ 5) ℓ : ℝ)) * (ℓ : ℝ) ^ (-s))
      + (2 * (Nat.card {τ : L ≃ₐ[ℚ] L | IsConj σ τ} : ℝ) / (Nat.card (L ≃ₐ[ℚ] L) : ℝ))
        * Real.log (s - 1))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_towerDirichletDensity_add_of_orderOf_eq_eight.solution
