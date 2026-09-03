import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_ne_zero

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicInduction.exists_isWhittakerFunctional3_ne_zero (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hχ : ∀ i, IsLocallyConstant (χ i))
    (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψball : ∃ m : ℤ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp m → ψv x = 1) :
    ∃ L : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ, L ≠ 0 ∧ IsWhittakerFunctional3 ψv L := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_ne_zero.solution
