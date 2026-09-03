import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_PeriodDatum_U_divisible

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.PeriodDatum.U_divisible
    {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
    {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}
    (P : PeriodDatum D K L ord) (hroots : ∀ (x : Lˣ) (n : ℕ), 0 < n → ∃ y : Lˣ, y ^ n = x) :
    ∀ u : ↥P.U, ∀ n : ℕ, 0 < n → ∃ u' : ↥P.U, n • u' = u := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_PeriodDatum_U_divisible.solution
