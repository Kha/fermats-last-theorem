import Mathlib
import P2M.Util
namespace P2MW.S_HomogeneousIdeal_irrelevant_le_map_of_forall_le_span_image

set_option autoImplicit false

universe u

theorem solution
    {S : Type u} [CommRing S] {S' : Type u} [CommRing S']
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (R' : Type u) [CommRing R'] [Algebra S' R'] (𝓡' : ℕ → Submodule S' R') [GradedAlgebra 𝓡']
    (ϑ : R →+* R') (hϑdeg : ∀ n, ∀ x ∈ 𝓡 n, ϑ x ∈ 𝓡' n)
    (hspan : ∀ n, 0 < n → 𝓡' n ≤ Submodule.span S' (ϑ '' (𝓡 n : Set R))) :
    HomogeneousIdeal.irrelevant 𝓡' ≤
      (HomogeneousIdeal.irrelevant 𝓡).map ({ ϑ with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡') := by
  classical
  refine toIdeal_le_toIdeal_iff.mp fun x hx => ?_
  rw [HomogeneousIdeal.toIdeal_map]
  rw [← DirectSum.sum_support_decompose 𝓡' x]
  refine Ideal.sum_mem _ fun n _ => ?_
  by_cases h0 : n = 0
  · subst h0
    have h00 : (DirectSum.decompose 𝓡' x 0 : R') = 0 := by
      simpa [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] using hx
    rw [h00]
    exact Ideal.zero_mem _
  · have hmem : (DirectSum.decompose 𝓡' x n : R') ∈ Submodule.span S' (ϑ '' (𝓡 n : Set R)) :=
      hspan n (Nat.pos_of_ne_zero h0) (DirectSum.decompose 𝓡' x n).2
    have hT : ϑ '' (𝓡 n : Set R) ⊆
        ((((HomogeneousIdeal.irrelevant 𝓡).toIdeal.map
          ({ ϑ with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡')).restrictScalars S' : Submodule S' R') : Set R') := by
      rintro _ ⟨r, hr, rfl⟩
      exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem 𝓡 (Nat.pos_of_ne_zero h0) hr)
    exact Submodule.span_le.mpr hT hmem
