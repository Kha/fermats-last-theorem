import Mathlib
import P2M.Util
import P2M.Sol.S_Ring_DimensionLEOne_of_finiteType_of_trdeg_le_one

set_option autoImplicit false

theorem Ring.DimensionLEOne.of_finiteType_of_trdeg_le_one
    (k : Type*) (B : Type*) [Field k] [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    (htr : Algebra.trdeg k B ≤ 1) : Ring.DimensionLEOne B := by p2m_exact_reverting @_root_.P2MW.S_Ring_DimensionLEOne_of_finiteType_of_trdeg_le_one.solution
