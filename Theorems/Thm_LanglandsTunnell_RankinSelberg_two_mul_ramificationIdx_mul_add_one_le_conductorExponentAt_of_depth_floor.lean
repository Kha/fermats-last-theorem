import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_two_mul_ramificationIdx_mul_add_one_le_conductorExponentAt_of_depth_floor

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.RankinSelberg
open scoped nonZeroDivisors

theorem LanglandsTunnell.RankinSelberg.two_mul_ramificationIdx_mul_add_one_le_conductorExponentAt_of_depth_floor
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (N : Ideal (𝓞 ℚ))
    (hfloor : ∀ w ∈ primeFibre ℚ K p,
      4 * (FractionalIdeal.count K w
            ((N.map (algebraMap (𝓞 ℚ) (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) +
          LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 1) ≤
        LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w))
    (b : ℕ)
    (hNb : p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N) :
              (∀ w ∈ primeFibre ℚ K p,
            2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b) + 1 ≤
              LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_two_mul_ramificationIdx_mul_add_one_le_conductorExponentAt_of_depth_floor.solution
