import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import P2M.Util
import P2M.Sol.S_AutomorphicForm_archCasimirAtComplex_rightTranslate_archComplexGLAt

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.archCasimirAtComplex_rightTranslate_archComplexGLAt
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAtComplex hw x)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) :
    ∀ m : GL (Fin 2) ℂ,
        IsArchSmoothAtComplex hw (rightTranslate K (archComplexGLAt hw m) x) ∧
        (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d (rightTranslate K (archComplexGLAt hw m) x))) ∧
        (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d'
          (rightTranslate K (archComplexGLAt hw m) x)))) ∧
        archCasimirAtComplex hw (rightTranslate K (archComplexGLAt hw m) x) =
          rightTranslate K (archComplexGLAt hw m) (archCasimirAtComplex hw x) ∧
        archCasimirBarAtComplex hw (rightTranslate K (archComplexGLAt hw m) x) =
          rightTranslate K (archComplexGLAt hw m) (archCasimirBarAtComplex hw x) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_archCasimirAtComplex_rightTranslate_archComplexGLAt.solution
