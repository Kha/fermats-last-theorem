import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_exists_gamma0_forall_tendsto_slash_atImInfty_of_three_le

set_option autoImplicit false

open scoped MatrixGroups ModularForm Topology

theorem ModularForm.exists_gamma0_forall_tendsto_slash_atImInfty_of_three_le (N : ℕ) [NeZero N] (k : ℤ)
    (hk : 3 ≤ k) (hke : Even k) (v : SL(2, ℤ) → ℂ)
    (hv : ∀ (σ γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 N → ∀ j : ℤ, v (γ * σ * ModularGroup.T ^ j) = v σ) :
    ∃ f : ModularForm (CongruenceSubgroup.Gamma0 N) k, ∀ σ : SL(2, ℤ),
      Filter.Tendsto (fun τ => ((⇑f) ∣[k] σ) τ) UpperHalfPlane.atImInfty (𝓝 (v σ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_gamma0_forall_tendsto_slash_atImInfty_of_three_le.solution
