import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_ArchDatumR_norm_W_diagOne_mul_inv_le_of_iwasawa

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.Converse.ArchDatumR.norm_W_diagOne_mul_inv_le_of_iwasawa
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (a : ℝ) (ha : a ≠ 0) :
    ∀ N : ℕ, ∃ C σ₀ : ℝ, 0 ≤ C ∧ 0 ≤ σ₀ ∧
      ∀ (t : ℝ) (e : Matrix (Fin 2) (Fin 2) ℝ), t ≠ 0 → e.det ≠ 0 →
        ‖D.W (ArchR.diagOne (a * t) * e⁻¹)‖ ≤
          C * Real.sqrt (∑ i, (e⁻¹ 1 i) ^ 2) ^ (P₂.centralExponent.re + 1) *
            ((|a * t| / (|e.det| * ∑ i, (e⁻¹ 1 i) ^ 2)) ^ (-(N : ℝ)) +
              (|a * t| / (|e.det| * ∑ i, (e⁻¹ 1 i) ^ 2)) ^ (-σ₀)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_ArchDatumR_norm_W_diagOne_mul_inv_le_of_iwasawa.solution
