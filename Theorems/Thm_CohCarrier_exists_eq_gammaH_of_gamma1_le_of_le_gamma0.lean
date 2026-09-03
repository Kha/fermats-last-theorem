import Mathlib
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_eq_gammaH_of_gamma1_le_of_le_gamma0

set_option autoImplicit false

open scoped MatrixGroups

theorem CohCarrier.exists_eq_gammaH_of_gamma1_le_of_le_gamma0
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M) :
    ∃ H : Subgroup (ZMod M)ˣ, Γ = CohCarrier.GammaH M H := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_eq_gammaH_of_gamma1_le_of_le_gamma0.solution
