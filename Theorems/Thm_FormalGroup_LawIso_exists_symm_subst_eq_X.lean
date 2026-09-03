import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_LawIso_exists_symm_subst_eq_X

set_option autoImplicit false

open FormalGroup IsLocalRing

universe u

theorem FormalGroup.LawIso.exists_symm_subst_eq_X
    {R : Type u} [CommRing R] {F G : FormalGroup R} (ψ : FormalGroup.LawIso F G) :
    ∃ ψ' : FormalGroup.LawIso G F,
      PowerSeries.subst ψ.series ψ'.series = PowerSeries.X ∧
        PowerSeries.subst ψ'.series ψ.series = PowerSeries.X := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_LawIso_exists_symm_subst_eq_X.solution
