import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Mathlib.GroupTheory.Abelianization.Defs
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_exists_periodDatum_apply_eq_of_surjective_of_forall_ker

set_option autoImplicit false

theorem CerednikDrinfeld.Mumford.exists_periodDatum_apply_eq_of_surjective_of_forall_ker
    {E V : Type} [Fintype E] [DecidableEq V] (D : CerednikDrinfeld.DegeneracyData E V)
    {G : Type} [Group G] (Φ : Additive (Abelianization G) →+ ↥(CerednikDrinfeld.ribbonKernel D))
    (hΦ : Function.Surjective Φ)
    (F L : Type) [Field F] [Field L] [Algebra F L] (ord : Additive Fˣ →+ ℤ)
    (Qh : G →* G →* Fˣ) (hsymm : ∀ α β : G, Qh α β = Qh β α)
    (hker : ∀ α : G, Φ (Additive.ofMul (Abelianization.of α)) = 0 → ∀ β : G, Qh α β = 1)
    (hord : ∀ α β : G, ord (Additive.ofMul (Qh α β)) =
      ∑ e : E, (D.w e : ℤ) * ((Φ (Additive.ofMul (Abelianization.of α)) : E → ℤ) e *
                              (Φ (Additive.ofMul (Abelianization.of β)) : E → ℤ) e)) :
    ∃ P : CerednikDrinfeld.Mumford.PeriodDatum D F L ord,
      ∀ α β : G, P.Q (Φ (Additive.ofMul (Abelianization.of α))) (Φ (Additive.ofMul (Abelianization.of β))) =
        Additive.ofMul (Qh α β) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_exists_periodDatum_apply_eq_of_surjective_of_forall_ker.solution
