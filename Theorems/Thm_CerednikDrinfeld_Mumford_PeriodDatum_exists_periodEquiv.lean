import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_PeriodDatum_exists_periodEquiv

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.PeriodDatum.exists_periodEquiv
    {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
    {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}
    (P : PeriodDatum D K L ord) :
    ∃ e : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(LinearMap.ker P.π),
      ∀ x : ↥(ribbonKernel D), ((e x : ↥P.U) : P.TorusPoints) = P.QL x := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_PeriodDatum_exists_periodEquiv.solution
