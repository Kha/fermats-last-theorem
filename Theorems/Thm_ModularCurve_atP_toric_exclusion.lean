import Mathlib.LinearAlgebra.Determinant
import P2M.Util
import P2M.Sol.S_ModularCurve_atP_toric_exclusion

namespace ModularCurve
theorem atP_toric_exclusion {G : Type*} [Group G]
    {J : Type*} [AddCommGroup J] [DistribMulAction G J]
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [DistribMulAction G V] [SMulCommClass G k V]
    {I : Subgroup G} {n : G → ℕ} {W : AddSubgroup J}
    (hmult : ∀ σ ∈ I, ∀ x ∈ W, σ • x = n σ • x)
    (ι : V →+ J) (hinj : Function.Injective ι)
    (hequiv : ∀ (g : G) (v : V), ι (g • v) = g • ι v)
    (hsub : ∀ v : V, ι v ∈ W) (hrank : Module.finrank k V = 2)
    (hdet : ∀ σ ∈ I, LinearMap.det (DistribMulAction.toLinearMap k V σ) = (n σ : k))
    (hunit : ∀ σ ∈ I, (n σ : k) ≠ 0) (hram : ∃ σ ∈ I, (n σ : k) ≠ 1) :
    False := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_atP_toric_exclusion.solution
end ModularCurve
