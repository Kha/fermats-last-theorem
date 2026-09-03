import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_LawHom_subst_nthSeries_series_eq

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.LawHom.subst_nthSeries_series_eq
    {R : Type*} [CommRing R] {F' F : FormalGroup R} (ψ : FormalGroup.LawHom F' F) (n : ℕ) :
    PowerSeries.subst (F'.nthSeries n) ψ.series = PowerSeries.subst ψ.series (F.nthSeries n) := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_LawHom_subst_nthSeries_series_eq.solution
