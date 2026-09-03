import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
namespace P2MW.S_Rep_nonempty_tateH0_linearEquiv_homology_normHomCompSub

set_option autoImplicit false
universe u
open CategoryTheory Rep

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

theorem solution
    {k G : Type u} [CommRing k] [CommGroup G] [Fintype G] (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nonempty (A.tateH0 ≃ₗ[k] (FiniteCyclicGroup.normHomCompSub A g).homology) := by

  have hker : A.ρ.invariants = LinearMap.ker (FiniteCyclicGroup.normHomCompSub A g).g.hom := by
    ext x
    rw [Representation.mem_invariants, LinearMap.mem_ker]
    change (∀ h : G, A.ρ h x = x) ↔ A.ρ g x - x = 0
    rw [sub_eq_zero]
    refine ⟨fun h => h g, fun h γ => ?_⟩
    obtain ⟨n, rfl⟩ := mem_powers_iff_mem_zpowers.2 (hg γ)
    rw [map_pow, Module.End.pow_apply]
    exact Function.iterate_fixed h n

  have hmap : (LinearMap.range A.ρ.normBar).map
      ((LinearEquiv.ofEq _ _ hker : A.ρ.invariants ≃ₗ[k] _) : A.ρ.invariants →ₗ[k] _) =
      LinearMap.range (FiniteCyclicGroup.normHomCompSub A g).moduleCatToCycles := by
    apply le_antisymm
    · rintro _ ⟨z, ⟨c, rfl⟩, rfl⟩
      obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ c
      exact ⟨v, Subtype.ext (by simp)⟩
    · rintro _ ⟨v, rfl⟩
      exact ⟨A.ρ.normBar (Representation.Coinvariants.mk _ v), ⟨_, rfl⟩, Subtype.ext (by simp)⟩
  exact ⟨(Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ hker) hmap).trans
    (FiniteCyclicGroup.normHomCompSub A g).moduleCatHomologyIso.toLinearEquiv.symm⟩
