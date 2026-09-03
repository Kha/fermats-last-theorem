import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_AdelicTraceFin
import P2M.Util
import P2M.Sol.S_NumberField_AdelicLevel_diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm IsDedekindDomain

open scoped Classical in

theorem NumberField.AdelicLevel.diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (a : (AdeleRing (𝓞 K) K)ˣ) (ha : ((a : (AdeleRing (𝓞 K) K))).2 = 1) (x : ℝ) :
    diagOne a * archRealGLAt hw (unipotentGL2 x) =
        unipotentGL2 (show (AdeleRing (𝓞 K) K) from (Pi.single w (((a : (AdeleRing (𝓞 K) K))).1 w *
            (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm x), 0)) * diagOne a ∧
      NumberField.StandardAddChar.stdAddChar K
        (show (AdeleRing (𝓞 K) K) from (Pi.single w ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm (1 / 2)), 0)) = -1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicLevel_diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half.solution
