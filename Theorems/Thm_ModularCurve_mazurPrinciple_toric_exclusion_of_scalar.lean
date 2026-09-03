import Mathlib
import Definitions.Def_ModularCurve_DeligneRapoport
import P2M.Util
import P2M.Sol.S_ModularCurve_mazurPrinciple_toric_exclusion_of_scalar

theorem ModularCurve.mazurPrinciple_toric_exclusion_of_scalar
    {G : Type*} [Group G]
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [DistribMulAction G V] [SMulCommClass G k V]
    {R : Type*} [CommRing R]
    {J : Type*} [AddCommGroup J] [Module R J] [DistribMulAction G J]
    {q : ℕ} {φ : G} {𝒯 : Submodule R J}
    (hfrob : ModularCurve.ToricFrobeniusSq q φ 𝒯)
    (ι : V →+ J) (hinj : Function.Injective ι)
    (hequiv : ∀ g : G, ∀ v : V, ι (g • v) = g • ι v)
    (hsub : ∀ v : V, ι v ∈ 𝒯)
    (lam : k) (hscalar : ∀ v : V, φ • v = lam • v)
    (hrank : Module.finrank k V = 2)
    (hdet : LinearMap.det (DistribSMul.toLinearMap k V φ) = (q : k)) :
    (q : k) = 0 ∨ (q : k) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_mazurPrinciple_toric_exclusion_of_scalar.solution
