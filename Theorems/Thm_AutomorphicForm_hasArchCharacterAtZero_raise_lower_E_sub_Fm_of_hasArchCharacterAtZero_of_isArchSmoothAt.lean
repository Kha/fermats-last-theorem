import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_hasArchCharacterAtZero_raise_lower_E_sub_Fm_of_hasArchCharacterAtZero_of_isArchSmoothAt

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
p2m_open "AutomorphicForm~hasDerivAt_apply_mul_archRealGLAt_inv_mul_archFlowMatrix_mul AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent"
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.hasArchCharacterAtZero_raise_lower_E_sub_Fm_of_hasArchCharacterAtZero_of_isArchSmoothAt
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (n : ℤ)
    (ψ : AdelicGL2 (𝓞 K) K → ℂ) (hψ : IsArchSmoothAt hw ψ)
    (hwt : HasArchCharacterAt₀ K w (archWeightCharAt hw n) ψ) :
    HasArchCharacterAt₀ K w (archWeightCharAt hw (n + 2))
        (archDerivAt hw .H ψ + Complex.I • (archDerivAt hw .E ψ + archDerivAt hw .Fm ψ)) ∧
      HasArchCharacterAt₀ K w (archWeightCharAt hw (n - 2))
        (archDerivAt hw .H ψ - Complex.I • (archDerivAt hw .E ψ + archDerivAt hw .Fm ψ)) ∧
      HasArchCharacterAt₀ K w (archWeightCharAt hw n) (archDerivAt hw .E ψ - archDerivAt hw .Fm ψ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_hasArchCharacterAtZero_raise_lower_E_sub_Fm_of_hasArchCharacterAtZero_of_isArchSmoothAt.solution
