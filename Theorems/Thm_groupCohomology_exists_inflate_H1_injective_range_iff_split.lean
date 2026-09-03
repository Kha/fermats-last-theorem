import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_inflate_H1_injective_range_iff_split

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.exists_inflate_H1_injective_range_iff_split
    {k : Type} [CommRing k] (M : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (β : B →+ M) (hβ : Function.Bijective β)
    (hβeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B),
      β (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) = M.ρ γ (β b)) :
    ∃ infl : groupCohomology B 1 →+ H1 M,
      (∀ (n : cocycles₁ B) (ny : cocycles₁ M),
        (∀ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ny γ = β (n (AlgEquiv.restrictNormalHom ↥F γ))) →
          infl ((H1π B).hom n) = (H1π M).hom ny) ∧
      Function.Injective infl ∧
      (∀ y : H1 M, (∃ x, infl x = y) ↔
        ∃ ny : cocycles₁ M, (H1π M).hom ny = y ∧
          (∀ (γ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F.fixingSubgroup → ny (γ * s) = ny γ) ∧
          (∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ F.fixingSubgroup → ny s = 0)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_inflate_H1_injective_range_iff_split.solution
