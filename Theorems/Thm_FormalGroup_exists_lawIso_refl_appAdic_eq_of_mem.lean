import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_exists_lawIso_refl_appAdic_eq_of_mem

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.exists_lawIso_refl_appAdic_eq_of_mem
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R] (F : FormalGroup R) :
    ∃ ψ : FormalGroup.LawIso F F, ψ.series = PowerSeries.X ∧ ∀ y ∈ I, ψ.toLawHom.appAdic I y = y := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_exists_lawIso_refl_appAdic_eq_of_mem.solution
