import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_CupProduct
import P2M.Util
import P2M.Sol.S_groupCohomology_cup_mem_levelCocycles2

set_option autoImplicit false
universe u
open CategoryTheory groupCohomology
theorem groupCohomology.cup_mem_levelCocycles2
    {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {A B N : Rep.{u} k G} (φ : A →ₗ[k] B →ₗ[k] N) (hφ : Rep.IsEquivariantBilinear A B N φ)
    (hB : ∀ b : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → B.ρ s b = b)
    (f : cocycles₁ A) (g : cocycles₁ B)
    (hf : IsLevelConstant₁ r (⇑f)) (hg : IsLevelConstant₁ r (⇑g)) :
    (cup φ hφ f g : G × G → N) ∈ levelCocycles₂ r N := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_cup_mem_levelCocycles2.solution
