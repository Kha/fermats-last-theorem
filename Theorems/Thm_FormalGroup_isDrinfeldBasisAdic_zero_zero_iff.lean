import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_isDrinfeldBasisAdic_zero_zero_iff

set_option autoImplicit false

open FormalGroup

theorem FormalGroup.isDrinfeldBasisAdic_zero_zero_iff
    {T : Type*} [CommRing T] (I : Ideal T) [IsAdicComplete I T] (F : FormalGroup T) (q : ℕ) :
    F.IsDrinfeldBasisAdic I q 0 0 ↔
      ∃ u : PowerSeries T, IsUnit u ∧ F.nthSeries q = u * PowerSeries.X ^ (q * q) := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_isDrinfeldBasisAdic_zero_zero_iff.solution
