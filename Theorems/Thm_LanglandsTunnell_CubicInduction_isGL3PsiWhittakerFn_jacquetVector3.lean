import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_jacquetVector3

set_option autoImplicit false
open NumberField LanglandsTunnell.Converse
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.isGL3PsiWhittakerFn_jacquetVector3
    (P : RealArchParam) (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2)
    (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    :
      IsGL3PsiWhittakerFn psiInf (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_jacquetVector3.solution
