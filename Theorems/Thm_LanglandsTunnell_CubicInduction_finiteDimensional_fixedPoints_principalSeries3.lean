import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_finiteDimensional_fixedPoints_principalSeries3

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.finiteDimensional_fixedPoints_principalSeries3
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (n : ℕ) :
    FiniteDimensional ℂ ↥(principalSeries3 v χ ⊓
      ⨅ k ∈ {k : LocalGL3 v | ∀ i j : Fin 3,
          Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
            ≤ WithZero.exp (-(n : ℤ))},
        LinearMap.ker (gl3AmbientRightTranslate (R := ℂ) k - LinearMap.id)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_fixedPoints_principalSeries3.solution
