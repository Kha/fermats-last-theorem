import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_PeriodPair_Uniformization
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_mem_GammaH_smul_eq_of_forall_sum_weierstrassP_pow_eq

set_option autoImplicit false

open scoped MatrixGroups

theorem CohCarrier.exists_mem_GammaH_smul_eq_of_forall_sum_weierstrassP_pow_eq (N : ℕ) [NeZero N]
    (H : Subgroup (ZMod N)ˣ) [Fintype H] (τ : UpperHalfPlane)
    (γ₀ : SL(2, ℤ)) (hγ₀ : γ₀ ∈ CongruenceSubgroup.Gamma0 N) (d : ℕ)
    (hd : d = 1 ∨ (d = 2 ∧ (PeriodPair.ofTau τ).g₃ = 0) ∨ (d = 3 ∧ (PeriodPair.ofTau τ).g₂ = 0))
    (hsum : ∀ j : ℕ, 0 < j →
      ∑ h : H, (PeriodPair.ofTau τ).weierstrassP ((((h : (ZMod N)ˣ) : ZMod N).val : ℂ) / N) ^ (d * j) =
        ∑ h : H, (PeriodPair.ofTau τ).weierstrassP
          ((((CohCarrier.gamma0Units N ⟨γ₀, hγ₀⟩ * (h : (ZMod N)ˣ) : (ZMod N)ˣ) : ZMod N).val : ℂ) / N) ^
            (d * j)) :
    ∃ γ ∈ CohCarrier.GammaH N H, γ • τ = γ₀ • τ := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_mem_GammaH_smul_eq_of_forall_sum_weierstrassP_pow_eq.solution
