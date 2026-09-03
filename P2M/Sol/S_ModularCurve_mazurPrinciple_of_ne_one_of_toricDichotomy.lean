import Mathlib
import Definitions.Def_ModularCurve_ToricDichotomyData
import Theorems.Thm_ModularCurve_mazurPrinciple_toric_exclusion_of_scalar
import P2M.Util
namespace P2MW.S_ModularCurve_mazurPrinciple_of_ne_one_of_toricDichotomy

open ModularCurve

theorem solution
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
    ModularCurve.HasLowerLevelTorsion S 𝔪 J₀ := by
  by_cases hsub : ∀ v : V, ι v ∈ 𝒯
  ·
    obtain ⟨lam, hlam⟩ := hscalar hsub
    rcases ModularCurve.mazurPrinciple_toric_exclusion_of_scalar hfrob ι hinj hequiv hsub
      lam hlam hrank hdet with h0 | h1
    · exact absurd h0 hq0
    · exact absurd h1 hq1
  ·
    obtain ⟨v, hv⟩ := not_forall.mp hsub
    have hinv : ∀ σ ∈ I, σ • ι v = ι v := fun σ hσ => by rw [← hequiv, hunr σ hσ]
    rcases hdich 𝔪 hmax heis hqu (ι v) (htors v) hinv with hmem | hlow
    · exact absurd hmem hv
    · exact hlow
