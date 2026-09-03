import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_exists_mem_higherUnitsAt_pow_two_ne_one_and_pow_three_ne_one_of_hasConductorExponentAt

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.TateLocal.exists_mem_higherUnitsAt_pow_two_ne_one_and_pow_three_ne_one_of_hasConductorExponentAt
    (p : HeightOneSpectrum (𝓞 ℚ)) (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (kp : ℕ)
    (hkp : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p χ kp)
    (m : ℕ) (hm : m + 4 ≤ kp) :
    (∃ s ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p m, χ s ^ 2 ≠ 1) ∧
    (∃ s ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p m, χ s ^ 3 ≠ 1) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_exists_mem_higherUnitsAt_pow_two_ne_one_and_pow_three_ne_one_of_hasConductorExponentAt.solution
