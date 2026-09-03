import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_mul_dual_eq_of_isGL3PsiWhittakerFn_inv_of_unipotent

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
open scoped nonZeroDivisors

theorem LanglandsTunnell.CubicInduction.mul_dual_eq_of_isGL3PsiWhittakerFn_inv_of_unipotent
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (F : LocalGL3 v → ℂ) (hF : IsGL3PsiWhittakerFn ψv⁻¹ F)
    (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂ (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
    (x : v.adicCompletion ℚ) (X : LocalGL3 v) (h : GL (Fin 2) (v.adicCompletion ℚ)) :
    F (iotaGL (UnramifiedWhittaker.unipotent x) * X) *
        W₂ ((AutomorphicForm.gl2Weyl : GL (Fin 2) (v.adicCompletion ℚ)) *
          AutomorphicForm.transposeInvN (Fin 2) (UnramifiedWhittaker.unipotent x * h)) =
      F X *
        W₂ ((AutomorphicForm.gl2Weyl : GL (Fin 2) (v.adicCompletion ℚ)) *
          AutomorphicForm.transposeInvN (Fin 2) h) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_mul_dual_eq_of_isGL3PsiWhittakerFn_inv_of_unipotent.solution
