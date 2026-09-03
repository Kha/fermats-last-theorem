import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_principalSeries2_apply_one_eq_zero_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_principalSeries2_apply_one_eq_zero_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator
    (p : HeightOneSpectrum (𝓞 ℚ)) (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (c : Fin 2 → ℕ)
    (hcθ : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), θ i u = 1) :
    (∃ φ : ℤ → p.adicCompletion ℚ → ↥(principalSeries2 p θ),
      (∀ (n : ℤ) (t : p.adicCompletion ℚ), (φ n t : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) 1 = 0) ∧
      (∀ (n : ℤ) (t x : p.adicCompletion ℚ),
        (φ n t : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (antidiagonal2 p * upperUnipotent2 p x) =
          if Valued.v (x - t) ≤ WithZero.exp (-n) then 1 else 0)) ∧
    ∃ ψ : ↥(principalSeries2 p θ), (ψ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) 1 = 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_principalSeries2_apply_one_eq_zero_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator.solution
