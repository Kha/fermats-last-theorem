import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_WhittakerBlock_hasDerivAt_apply_mul_archRealLift3_of_isArchSmooth3
attribute [-simp] LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.WhittakerBlock.hasDerivAt_apply_mul_archRealLift3_of_isArchSmooth3
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : WhittakerBlock.IsArchSmooth3 F) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3)
    (s : ℝ) (hs : 1 + (if i = j then s else 0) ≠ 0) :
    HasDerivAt
      (fun r : ℝ => F (g * WhittakerBlock.archRealLift3 (fun a b =>
        (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then r else 0)))
      ((((1 + (if i = j then s else 0))⁻¹ : ℝ) : ℂ) *
        WhittakerBlock.archDeriv i j F (g * WhittakerBlock.archRealLift3 (fun a b =>
          (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0)))
      s := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_hasDerivAt_apply_mul_archRealLift3_of_isArchSmooth3.solution
