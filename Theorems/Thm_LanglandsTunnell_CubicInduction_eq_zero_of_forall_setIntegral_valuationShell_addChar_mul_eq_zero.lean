import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_eq_zero_of_forall_setIntegral_valuationShell_addChar_mul_eq_zero
attribute [-simp] LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.eq_zero_of_forall_setIntegral_valuationShell_addChar_mul_eq_zero
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (hψv : ψv ≠ 1)
    (hψloc : ∃ n : ℤ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → ψv x = 1)
    (k : ℤ) (h : (v.adicCompletion ℚ)ˣ → ℂ) (m : ℕ)
    (hloc : ∀ a b : (v.adicCompletion ℚ)ˣ, Valued.v (a : v.adicCompletion ℚ) = WithZero.exp (-k) →
      Valued.v ((b : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-((m : ℤ) + 1)) → h (a * b) = h a)
    (hzero : letI := localBorel ℚ v
      ∀ y : v.adicCompletion ℚ,
        ∫ a in {a : (v.adicCompletion ℚ)ˣ | Valued.v (a : v.adicCompletion ℚ) = WithZero.exp (-k)},
          ψv (y * (a : v.adicCompletion ℚ)) * h a ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) = 0) :
    ∀ a : (v.adicCompletion ℚ)ˣ, Valued.v (a : v.adicCompletion ℚ) = WithZero.exp (-k) → h a = 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_forall_setIntegral_valuationShell_addChar_mul_eq_zero.solution
