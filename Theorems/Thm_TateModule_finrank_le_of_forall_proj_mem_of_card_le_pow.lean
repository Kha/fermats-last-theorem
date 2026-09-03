import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_TateModule_finrank_le_of_forall_proj_mem_of_card_le_pow

set_option autoImplicit false

open scoped TensorProduct

theorem TateModule.finrank_le_of_forall_proj_mem_of_card_le_pow
    (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] (r : ℕ)
    (K : Submodule ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] TateModule p M))
    (B : ℕ → Finset M) (hB : ∀ k, (B k).card ≤ p ^ (k * r))
    (hK : ∀ x : TateModule p M, (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x ∈ K → ∀ k, TateModule.proj p M k x ∈ B k) :
    Module.finrank ℚ_[p] K ≤ r := by p2m_exact_reverting @_root_.P2MW.S_TateModule_finrank_le_of_forall_proj_mem_of_card_le_pow.solution
