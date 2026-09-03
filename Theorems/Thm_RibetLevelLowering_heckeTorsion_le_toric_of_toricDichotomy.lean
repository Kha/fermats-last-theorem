import Mathlib
import Definitions.Def_ModularCurve_ToricDichotomyData
import P2M.Util
import P2M.Sol.S_RibetLevelLowering_heckeTorsion_le_toric_of_toricDichotomy
set_option autoImplicit false
open ModularCurve

theorem RibetLevelLowering.heckeTorsion_le_toric_of_toricDichotomy
    {G : Type*} [Group G] {I : Subgroup G}
    {J : Type*} [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]
    {J₀ : Type*} [AddCommGroup J₀] [Module HeckeAlg J₀]
    {q : ℕ} {S : Finset Nat.Primes} {𝒯 : Submodule HeckeAlg J}
    (hdich : IsToricDichotomyQGuarded q S I 𝒯 J₀)
    {𝔪 : Ideal HeckeAlg} (hmax : 𝔪.IsMaximal) (heis : ¬ IsEventuallyEisenstein 𝔪)
    (hqu : IsUnit ((q : ℕ) : HeckeAlg ⧸ 𝔪))
    (hunr : ∀ σ ∈ I, ∀ x ∈ heckeTorsion J 𝔪, σ • x = x)
    (hno : ¬ HasLowerLevelTorsion S 𝔪 J₀) :
    heckeTorsion J 𝔪 ≤ 𝒯 := by p2m_exact_reverting @_root_.P2MW.S_RibetLevelLowering_heckeTorsion_le_toric_of_toricDichotomy.solution
