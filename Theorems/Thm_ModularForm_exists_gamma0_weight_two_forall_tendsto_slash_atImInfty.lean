import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_exists_gamma0_weight_two_forall_tendsto_slash_atImInfty

set_option autoImplicit false

open scoped MatrixGroups ModularForm Topology

theorem ModularForm.exists_gamma0_weight_two_forall_tendsto_slash_atImInfty (N : ℕ) [NeZero N] (v : SL(2, ℤ) → ℂ)
    (hv : ∀ (σ γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 N → ∀ j : ℤ, v (γ * σ * ModularGroup.T ^ j) = v σ)
    (hsum : ∑ᶠ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, v q.out⁻¹ = 0) :
    ∃ f : ModularForm (CongruenceSubgroup.Gamma0 N) 2, ∀ σ : SL(2, ℤ),
      Filter.Tendsto (fun τ => ((⇑f) ∣[(2 : ℤ)] σ) τ) UpperHalfPlane.atImInfty (𝓝 (v σ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_gamma0_weight_two_forall_tendsto_slash_atImInfty.solution
