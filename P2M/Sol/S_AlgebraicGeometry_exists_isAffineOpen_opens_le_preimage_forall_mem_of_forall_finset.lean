import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_le_inf_forall_mem_of_finset
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X : Scheme.{u}}
    (hAF : ∀ G : Finset X, ∃ W : X.Opens, IsAffineOpen W ∧ ∀ x ∈ G, x ∈ W)
    (U O : X.Opens) (F : Finset ↥U) (hFO : ∀ x ∈ F, U.ι.base x ∈ O) :
    ∃ W : (U : Scheme.{u}).Opens, IsAffineOpen W ∧ W ≤ U.ι ⁻¹ᵁ O ∧ ∀ x ∈ F, x ∈ W := by
  classical
  obtain ⟨W₁, hW₁, hFW₁⟩ := hAF (F.image fun x => U.ι.base x)
  obtain ⟨W₂, hW₂, hle, hFW₂⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_le_inf_forall_mem_of_finset W₁ hW₁ (U ⊓ O)
      (F.image fun x => U.ι.base x) hFW₁ (by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact ⟨x.2, hFO x hx⟩)
  have hW₂U : W₂ ≤ U := (hle.trans inf_le_right).trans inf_le_left
  refine ⟨U.ι ⁻¹ᵁ W₂, hW₂.preimage_of_isOpenImmersion U.ι (by rwa [Scheme.Opens.opensRange_ι]), ?_, ?_⟩
  · exact Scheme.Hom.preimage_mono _ ((hle.trans inf_le_right).trans inf_le_right)
  · intro x hx
    exact hFW₂ _ (Finset.mem_image_of_mem _ hx)
