import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_LawHom_exists_comp_series_eq_subst

set_option autoImplicit false

open FormalGroup IsLocalRing

universe u

theorem FormalGroup.LawHom.exists_comp_series_eq_subst
    {R : Type u} [CommRing R] {F G H : FormalGroup R}
    (θ : FormalGroup.LawHom F G) (η : FormalGroup.LawHom G H) :
    ∃ κ : FormalGroup.LawHom F H, κ.series = PowerSeries.subst θ.series η.series ∧
      PowerSeries.coeff 1 κ.series = PowerSeries.coeff 1 η.series * PowerSeries.coeff 1 θ.series := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_LawHom_exists_comp_series_eq_subst.solution
