import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_archDerivAtComplex_Fm_sub_E_and_iE_add_iFm_eq_rightTranslate_iH_rightTranslate

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_archDerivAtComplex_Fm_sub_E_and_iE_add_iFm_eq_rightTranslate_iH_rightTranslate
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex) :
    ∃ k₁ k₂ : rowIsometrySubgroup₀ w.Completion,
      ∀ ψ : AdelicGL2 (𝓞 K) K → ℂ, IsArchSmoothAtComplex hw ψ →
        (archDerivAtComplex hw .Fm ψ - archDerivAtComplex hw .E ψ =
          rightTranslate K (rowIsometryInclAt₀ K w k₁)
            (archDerivAtComplex hw .iH (rightTranslate K (rowIsometryInclAt₀ K w k₁⁻¹) ψ))) ∧
        (archDerivAtComplex hw .iE ψ + archDerivAtComplex hw .iFm ψ =
          rightTranslate K (rowIsometryInclAt₀ K w k₂)
            (archDerivAtComplex hw .iH (rightTranslate K (rowIsometryInclAt₀ K w k₂⁻¹) ψ))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_archDerivAtComplex_Fm_sub_E_and_iE_add_iFm_eq_rightTranslate_iH_rightTranslate.solution
