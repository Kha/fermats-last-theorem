import Mathlib
import Definitions.Def_Module_CommFamilyAnnPart
import P2M.Util
import P2M.Sol.S_Module_End_CommFamily_finrank_inf_annPart_le_finrank_mul_of_forall_finrank_inf_iInf_ker_le

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

theorem Module.End.CommFamily.finrank_inf_annPart_le_finrank_mul_of_forall_finrank_inf_iInf_ker_le
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {σ : Type*}
    (F : Module.End.CommFamily K V σ) (p : ℕ) [Fact p.Prime] [CharP K p]
    {k₀ : Type*} [Field k₀] [Finite k₀] [Algebra (ZMod p) k₀]
    (θ₀ : σ → k₀) (hgen : Algebra.adjoin (ZMod p) (Set.range θ₀) = ⊤) (e : k₀ →+* K)
    (W : Submodule K V) (hW : ∀ (a : σ) (v : V), v ∈ W → F.T a v ∈ W) (d : ℕ)
    (hd : ∀ τ : k₀ →+* K,
      FiniteDimensional K ↥(W ⊓ ⨅ a : σ, LinearMap.ker (F.T a - τ (θ₀ a) • LinearMap.id)) ∧
        Module.finrank K ↥(W ⊓ ⨅ a : σ, LinearMap.ker (F.T a - τ (θ₀ a) • LinearMap.id)) ≤ d) :
    FiniteDimensional K ↥(W ⊓ F.annPart p (e ∘ θ₀)) ∧
      Module.finrank K ↥(W ⊓ F.annPart p (e ∘ θ₀)) ≤ Module.finrank (ZMod p) k₀ * d := by p2m_exact_reverting @_root_.P2MW.S_Module_End_CommFamily_finrank_inf_annPart_le_finrank_mul_of_forall_finrank_inf_iInf_ker_le.solution
