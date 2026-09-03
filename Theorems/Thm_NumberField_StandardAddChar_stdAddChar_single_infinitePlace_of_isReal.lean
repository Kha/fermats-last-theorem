import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NumberField_AdelicTraceFin
import P2M.Util
import P2M.Sol.S_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isReal

set_option autoImplicit false

open NumberField IsDedekindDomain

open scoped Classical in

theorem NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isReal
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (t : ℝ) :
    NumberField.StandardAddChar.stdAddChar K
        (show (AdeleRing (𝓞 K) K) from (Pi.single w ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t), 0)) =
      Complex.exp (2 * Real.pi * Complex.I * t) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isReal.solution
