import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem solution
    {B B₀ : Type u} [CommRing B] [CommRing B₀] (φ : B →+* B₀)
    (hφ : Function.Surjective φ) (hker : IsNilpotent (RingHom.ker φ))
    {X X₀ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (f₀ : X₀ ⟶ Spec (CommRingCat.of B₀))
    (g : X₀ ⟶ X) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom φ))) :
    IsClosedImmersion g ∧ Surjective g ∧ IsHomeomorph g.base := by

  have hci : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ) hφ

  have hsj : Surjective (Spec.map (CommRingCat.ofHom φ)) := by
    refine ⟨?_⟩
    rw [← Set.range_eq_univ]
    change Set.range (PrimeSpectrum.comap φ) = Set.univ
    rw [range_comap_of_surjective _ φ hφ, Set.eq_univ_iff_forall]
    intro p
    rw [PrimeSpectrum.mem_zeroLocus]
    intro x hx
    obtain ⟨n, hn⟩ := hker
    have hxn : IsNilpotent x := by
      refine ⟨n, ?_⟩
      have := Ideal.pow_mem_pow hx n
      rw [hn] at this
      simpa using this
    exact nilpotent_iff_mem_prime.mp hxn p.asIdeal inferInstance
  have h1 : IsClosedImmersion g := MorphismProperty.of_isPullback hg.flip hci
  have h2 : Surjective g := MorphismProperty.of_isPullback hg.flip hsj
  have h3 : IsHomeomorph g.base :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨g.isClosedEmbedding.isEmbedding, g.surjective⟩
  exact ⟨h1, h2, h3⟩
