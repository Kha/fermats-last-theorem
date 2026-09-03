import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_le_three_of_pow_two_eq_one

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_le_three_of_pow_two_eq_one
    (p : HeightOneSpectrum (𝓞 ℚ)) (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : ∀ x : (p.adicCompletion ℚ)ˣ, χ x ^ 2 = 1) :
    ∃ e : ℕ, e ≤ 3 ∧ LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p χ e := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_le_three_of_pow_two_eq_one.solution
