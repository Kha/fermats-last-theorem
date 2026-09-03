import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_diagUnitGL2_mul_eq_zero_of_lt_valued_of_isGL3PsiWhittakerFn
attribute [-simp] LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_forall_apply_iotaGL_diagUnitGL2_mul_eq_zero_of_lt_valued_of_isGL3PsiWhittakerFn
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (hψv : ψv ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (g : LocalGL3 v) :
    ∃ K : ℤ, ∀ a : (v.adicCompletion ℚ)ˣ, WithZero.exp K < Valued.v (a : v.adicCompletion ℚ) →
      W (iotaGL (diagUnitGL2 a) * g) = 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_diagUnitGL2_mul_eq_zero_of_lt_valued_of_isGL3PsiWhittakerFn.solution
