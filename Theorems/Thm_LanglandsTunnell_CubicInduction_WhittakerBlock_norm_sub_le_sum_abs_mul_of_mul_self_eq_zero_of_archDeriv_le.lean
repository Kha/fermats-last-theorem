import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_WhittakerBlock_norm_sub_le_sum_abs_mul_of_mul_self_eq_zero_of_archDeriv_le

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

open LanglandsTunnell.CubicInduction.WhittakerBlock (archDeriv)

theorem LanglandsTunnell.CubicInduction.WhittakerBlock.norm_sub_le_sum_abs_mul_of_mul_self_eq_zero_of_archDeriv_le
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : WhittakerBlock.IsArchSmooth3 F) (x : AdelicGL 3 (𝓞 ℚ) ℚ)
    (e : Fin 3 → Fin 3 → ℝ) (he : (Matrix.of e).det ≠ 0)
    (Y : Matrix (Fin 3) (Fin 3) ℝ) (hY : Y * Y = 0) (B : ℝ)
    (hB : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j : Fin 3,
      ‖archDeriv i j F (x * WhittakerBlock.archRealLift3 (fun a b => ((1 + s • Y) * Matrix.of e) a b))‖ ≤ B) :
    ‖F (x * WhittakerBlock.archRealLift3 e) -
        F (x * WhittakerBlock.archRealLift3 (fun a b => ((1 + Y) * Matrix.of e) a b))‖ ≤
      (∑ i : Fin 3, ∑ j : Fin 3, |((Matrix.of e)⁻¹ * Y * Matrix.of e) i j|) * B := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_norm_sub_le_sum_abs_mul_of_mul_self_eq_zero_of_archDeriv_le.solution
