import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_forall_finite_exists_isAffineOpen_of_isClosedImmersion_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {Z X : Scheme.{u}} (f : Z ⟶ X) [IsClosedImmersion f] [Surjective f]
    (hAff : ∀ U : X.Opens, IsAffineOpen (f ⁻¹ᵁ U) → IsAffineOpen U)
    (hZ : ∀ S : Set Z, S.Finite → ∃ U : Z.Opens, IsAffineOpen U ∧ S ⊆ (U : Set Z)) :
    ∀ S : Set X, S.Finite → ∃ U : X.Opens, IsAffineOpen U ∧ S ⊆ (U : Set X) := by
  intro S hS
  have hinj : Function.Injective f.base := f.isClosedEmbedding.injective
  have hsurj : Function.Surjective f.base := f.surjective
  obtain ⟨U₀, hU₀, hSU₀⟩ := hZ (f.base ⁻¹' S) (hS.preimage hinj.injOn)

  have hbij : Function.Bijective f.base := ⟨hinj, hsurj⟩
  have hopen : IsOpen (f.base '' (U₀ : Set Z)) := by
    rw [← compl_compl (f.base '' (U₀ : Set Z)), ← Set.image_compl_eq hbij]
    exact (f.isClosedEmbedding.isClosedMap _ U₀.isOpen.isClosed_compl).isOpen_compl
  let U : X.Opens := ⟨f.base '' (U₀ : Set Z), hopen⟩
  have hpre : f ⁻¹ᵁ U = U₀ := TopologicalSpace.Opens.ext (Set.preimage_image_eq _ hinj)
  refine ⟨U, hAff U (hpre ▸ hU₀), ?_⟩
  intro x hx
  obtain ⟨z, rfl⟩ := hsurj x
  exact ⟨z, hSU₀ hx, rfl⟩
