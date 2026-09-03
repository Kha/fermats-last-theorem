import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_coeff_nthSeries_eq_coeff_invDiff_of_isBaseChange

set_option autoImplicit false

open FormalGroup

theorem FormalGroup.coeff_nthSeries_eq_coeff_invDiff_of_isBaseChange
    (p : ℕ) [Fact p.Prime] {A R : Type*} [CommRing A] [CommRing R] [CharP R p]
    (hA : ∀ a : A, (p : A) * a = 0 → a = 0)
    (Fl : FormalGroup A) [Fl.IsComm] (f : A →+* R) (G : FormalGroup R) (hG : Fl.IsBaseChange f G) :
    PowerSeries.coeff p (G.nthSeries p) = PowerSeries.coeff (p - 1) G.invDiff := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_coeff_nthSeries_eq_coeff_invDiff_of_isBaseChange.solution
