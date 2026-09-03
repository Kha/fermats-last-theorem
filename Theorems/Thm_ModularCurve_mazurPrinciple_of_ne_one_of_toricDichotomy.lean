import Mathlib
import Definitions.Def_ModularCurve_ToricDichotomyData
import P2M.Util
import P2M.Sol.S_ModularCurve_mazurPrinciple_of_ne_one_of_toricDichotomy

theorem ModularCurve.mazurPrinciple_of_ne_one_of_toricDichotomy
    {G : Type*} [Group G] {I : Subgroup G}
    {J : Type*} [AddCommGroup J] [Module ModularCurve.HeckeAlg J] [DistribMulAction G J]
    {J₀ : Type*} [AddCommGroup J₀] [Module ModularCurve.HeckeAlg J₀]
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [DistribMulAction G V] [SMulCommClass G k V]
    {S : Finset Nat.Primes} {𝒯 : Submodule ModularCurve.HeckeAlg J}
    {q : ℕ} {φ : G}
    (hfrob : ModularCurve.ToricFrobeniusSq q φ 𝒯)
    (hdich : ModularCurve.IsToricDichotomyQGuarded q S I 𝒯 J₀)
    {𝔪 : Ideal ModularCurve.HeckeAlg} (hmax : 𝔪.IsMaximal)
    (heis : ¬ ModularCurve.IsEventuallyEisenstein 𝔪)
    (hqu : IsUnit ((q : ℕ) : ModularCurve.HeckeAlg ⧸ 𝔪))
    (ι : V →+ J) (hinj : Function.Injective ι)
    (hequiv : ∀ g : G, ∀ v : V, ι (g • v) = g • ι v)
    (htors : ∀ v : V, ι v ∈ ModularCurve.heckeTorsion J 𝔪)
    (hrank : Module.finrank k V = 2)
    (hdet : LinearMap.det (DistribSMul.toLinearMap k V φ) = (q : k))
    (hunr : ∀ σ ∈ I, ∀ v : V, σ • v = v)
    (hscalar : (∀ v : V, ι v ∈ 𝒯) → ∃ lam : k, ∀ v : V, φ • v = lam • v)
    (hq0 : (q : k) ≠ 0) (hq1 : (q : k) ≠ 1) :
    ModularCurve.HasLowerLevelTorsion S 𝔪 J₀ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_mazurPrinciple_of_ne_one_of_toricDichotomy.solution
