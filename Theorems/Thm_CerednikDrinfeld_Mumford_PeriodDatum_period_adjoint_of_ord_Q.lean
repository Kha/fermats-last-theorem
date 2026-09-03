import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_PeriodDatum_period_adjoint_of_ord_Q

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.PeriodDatum.period_adjoint_of_ord_Q
    {E V : Type} [Fintype E] [Fintype V] [DecidableEq V] {D : DegeneracyData E V}
    {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}
    (P : PeriodDatum D K L ord) (H : HeckeData D)
    (ℓ : Nat.Primes) (x y y' : ↥(ribbonKernel D))
    (h : ∀ z : ↥(ribbonKernel D), P.QL y (heckeKernelMap H ℓ z) = P.QL y' z) :
    ribbonGram D (heckeKernelMap H ℓ x) y = ribbonGram D x y' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_PeriodDatum_period_adjoint_of_ord_Q.solution
