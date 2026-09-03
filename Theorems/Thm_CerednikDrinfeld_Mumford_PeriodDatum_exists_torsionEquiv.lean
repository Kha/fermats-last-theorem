import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_PeriodDatum_exists_torsionEquiv

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.PeriodDatum.exists_torsionEquiv
    {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
    {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}
    (P : PeriodDatum D K L ord) {p : ℕ} [Fact p.Prime] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) :
    ∃ e : ↥(Submodule.torsionBy ℤ ↥P.U (p : ℤ)) ≃ₗ[ℤ] (↥(ribbonKernel D) →ₗ[ℤ] ZMod p),
      ∀ (v : ↥(Submodule.torsionBy ℤ ↥P.U (p : ℤ))) (z : ↥(ribbonKernel D)),
        ((v : ↥P.U) : P.TorusPoints) z = Additive.ofMul (ζ ^ (e v z).val) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_PeriodDatum_exists_torsionEquiv.solution
