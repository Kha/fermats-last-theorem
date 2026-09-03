import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_CupProduct
import P2M.Util
import P2M.Sol.S_groupCohomology_cup_mem_levelCoboundaries2_of_mem_coboundaries1_right

set_option autoImplicit false
universe u
open CategoryTheory groupCohomology
theorem groupCohomology.cup_mem_levelCoboundaries2_of_mem_coboundaries1_right
    {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {A B N : Rep.{u} k G} (φ : A →ₗ[k] B →ₗ[k] N) (hφ : Rep.IsEquivariantBilinear A B N φ)
    (f : cocycles₁ A) (g : cocycles₁ B) (hf : IsLevelConstant₁ r (⇑f))
    (b : B) (hb : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → B.ρ s b = b)
    (hg : ∀ s, g s = B.ρ s b - b) :
    (cup φ hφ f g : G × G → N) ∈ levelCoboundaries₂ r N := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_cup_mem_levelCoboundaries2_of_mem_coboundaries1_right.solution
