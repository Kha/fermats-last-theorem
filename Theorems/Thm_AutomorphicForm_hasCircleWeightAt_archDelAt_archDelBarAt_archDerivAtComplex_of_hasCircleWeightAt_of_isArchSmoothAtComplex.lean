import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_hasCircleWeightAt_archDelAt_archDelBarAt_archDerivAtComplex_of_hasCircleWeightAt_of_isArchSmoothAtComplex

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.hasCircleWeightAt_archDelAt_archDelBarAt_archDerivAtComplex_of_hasCircleWeightAt_of_isArchSmoothAtComplex
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex) (n : ℤ)
    (ψ : AdelicGL2 (𝓞 K) K → ℂ) (hψ : IsArchSmoothAtComplex hw ψ)
    (hwt : HasCircleWeightAt hw n ψ) :
    HasCircleWeightAt hw (n + 2) (archDelAt hw .E ψ) ∧
      HasCircleWeightAt hw (n - 2) (archDelBarAt hw .E ψ) ∧
      HasCircleWeightAt hw (n - 2) (archDelAt hw .Fm ψ) ∧
      HasCircleWeightAt hw (n + 2) (archDelBarAt hw .Fm ψ) ∧
      HasCircleWeightAt hw n (archDerivAtComplex hw .H ψ) ∧
      HasCircleWeightAt hw n (archDerivAtComplex hw .iH ψ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_hasCircleWeightAt_archDelAt_archDelBarAt_archDerivAtComplex_of_hasCircleWeightAt_of_isArchSmoothAtComplex.solution
