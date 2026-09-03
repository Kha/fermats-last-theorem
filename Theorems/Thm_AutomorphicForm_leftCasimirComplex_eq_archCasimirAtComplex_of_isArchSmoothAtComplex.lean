import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import P2M.Util
import P2M.Sol.S_AutomorphicForm_leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (θ : AdelicGL2 (𝓞 K) K → ℂ) (hθ : IsArchSmoothAtComplex hw θ) :
    let L : ArchDirComplex → (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun d γ y => deriv (fun t : ℝ => γ (archFlowAtComplex hw d (-t) * y)) 0
    ∀ y : AdelicGL2 (𝓞 K) K,
      -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * L .H (L .H θ) y + ((-Complex.I) : ℂ) * L .H (L .iH θ) y + ((-Complex.I) : ℂ) * L .iH (L .H θ) y + (-1 : ℂ) * L .iH (L .iH θ) y)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * L .H θ y + ((-Complex.I) : ℂ) * L .iH θ y)) + (1 / 4 : ℂ) * ((1 : ℂ) * L .E (L .Fm θ) y + ((-Complex.I) : ℂ) * L .E (L .iFm θ) y + ((-Complex.I) : ℂ) * L .iE (L .Fm θ) y + (-1 : ℂ) * L .iE (L .iFm θ) y)) = archCasimirAtComplex hw θ y ∧
      -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * L .H (L .H θ) y + (Complex.I : ℂ) * L .H (L .iH θ) y + (Complex.I : ℂ) * L .iH (L .H θ) y + (-1 : ℂ) * L .iH (L .iH θ) y)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * L .H θ y + (Complex.I : ℂ) * L .iH θ y)) + (1 / 4 : ℂ) * ((1 : ℂ) * L .E (L .Fm θ) y + (Complex.I : ℂ) * L .E (L .iFm θ) y + (Complex.I : ℂ) * L .iE (L .Fm θ) y + (-1 : ℂ) * L .iE (L .iFm θ) y)) = archCasimirBarAtComplex hw θ y := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex.solution
