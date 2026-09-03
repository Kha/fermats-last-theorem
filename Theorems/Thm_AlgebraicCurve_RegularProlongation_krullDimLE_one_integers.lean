import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_krullDimLE_one_integers

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.krullDimLE_one_integers
    {L : Type*} [Field L] (A : ValuationSubring L) [Ring.KrullDimLE 1 ↥A]
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) :
    Ring.KrullDimLE 1 ↥R.integers := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_krullDimLE_one_integers.solution
