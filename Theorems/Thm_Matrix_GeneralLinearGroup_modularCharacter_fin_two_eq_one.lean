import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_GeneralLinearGroup_modularCharacter_fin_two_eq_one

set_option autoImplicit false

open MeasureTheory

theorem Matrix.GeneralLinearGroup.modularCharacter_fin_two_eq_one
    {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace (GL (Fin 2) F)] (g : GL (Fin 2) F) :
    MeasureTheory.Measure.modularCharacter g = 1 := by p2m_exact_reverting @_root_.P2MW.S_Matrix_GeneralLinearGroup_modularCharacter_fin_two_eq_one.solution
