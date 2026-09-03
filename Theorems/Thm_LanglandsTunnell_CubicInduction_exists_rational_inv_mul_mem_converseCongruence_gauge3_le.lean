import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_rational_inv_mul_mem_converseCongruence_gauge3_le

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_rational_inv_mul_mem_converseCongruence_gauge3_le
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (a : HeightOneSpectrum (𝓞 ℚ) → ℕ) :
    ∃ (C : ℝ) (N : ℕ), ∀ x : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ γ : GL (Fin 3) ℚ,
      (∀ v ∈ S, componentAt3 (𝓞 ℚ) ℚ v ((globalPointsGL 3 (𝓞 ℚ) ℚ γ)⁻¹ * x) ∈ converseCongruenceSet3 v (a v)) ∧
      gauge3 ℚ ((globalPointsGL 3 (𝓞 ℚ) ℚ γ)⁻¹ * x) ≤ C * gauge3 ℚ x ^ N := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_rational_inv_mul_mem_converseCongruence_gauge3_le.solution
