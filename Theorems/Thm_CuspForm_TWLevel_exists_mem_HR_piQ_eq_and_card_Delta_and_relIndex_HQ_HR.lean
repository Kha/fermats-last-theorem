import Definitions.Def_CuspForm_TWLevelHeckeModule
import P2M.Util
import P2M.Sol.S_CuspForm_TWLevel_exists_mem_HR_piQ_eq_and_card_Delta_and_relIndex_HQ_HR

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open CuspForm.TWLevel

theorem CuspForm.TWLevel.exists_mem_HR_piQ_eq_and_card_Delta_and_relIndex_HQ_HR
    (N r : ℕ) [NeZero N] [NeZero r] (hr : r.Prime)
    {t : ℕ} (qv : Fin t → ℕ) [∀ i, NeZero (qv i)] (hqinj : Function.Injective qv)
    (hq : ∀ i, (qv i).Prime) (hqN : ∀ i, ¬ qv i ∣ N) (hqr : ∀ i, qv i ≠ r)
    (p : ℕ) [Fact p.Prime]
    (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))
    (hπΔ : ∀ i, Function.Surjective (πΔ i)) :
    (∀ δ : Delta qv p, ∃ u ∈ HR N r qv, piQ N r qv p πΔ u = δ) ∧
    Nat.card (Delta qv p) = p ^ ∑ i, padicValNat p (qv i - 1) ∧
    (HQ N r qv p πΔ).relIndex (HR N r qv) = p ^ ∑ i, padicValNat p (qv i - 1) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_TWLevel_exists_mem_HR_piQ_eq_and_card_Delta_and_relIndex_HQ_HR.solution
