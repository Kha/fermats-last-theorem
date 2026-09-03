import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_exists_lawIso_series_eq_of_isUnit_coeff_one

set_option autoImplicit false

open FormalGroup IsLocalRing

universe u

theorem FormalGroup.exists_lawIso_series_eq_of_isUnit_coeff_one
    {R : Type u} [CommRing R] (F : FormalGroup R) (u : PowerSeries R)
    (hu0 : PowerSeries.constantCoeff u = 0) (hu1 : IsUnit (PowerSeries.coeff 1 u)) :
    ∃ F' : FormalGroup R, (∃ ψ : FormalGroup.LawIso F F', ψ.series = u) ∧ (F.IsComm → F'.IsComm) ∧
      ∀ F'' : FormalGroup R, (∃ ψ : FormalGroup.LawIso F F'', ψ.series = u) → F'' = F' := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_exists_lawIso_series_eq_of_isUnit_coeff_one.solution
