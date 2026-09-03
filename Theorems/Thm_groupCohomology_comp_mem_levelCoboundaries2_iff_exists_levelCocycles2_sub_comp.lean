import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import P2M.Util
import P2M.Sol.S_groupCohomology_comp_mem_levelCoboundaries2_iff_exists_levelCocycles2_sub_comp

set_option autoImplicit false

universe u

open CategoryTheory
theorem groupCohomology.comp_mem_levelCoboundaries2_iff_exists_levelCocycles2_sub_comp {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) {A B C : Rep.{u} k G} (φ : A ⟶ B) (ψ : B ⟶ C)
    (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom) (hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b)
    (hsm : ∀ m : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → B.ρ s m = m)
    (b : G × G → B) (hb : b ∈ groupCohomology.levelCocycles₂ r B) :
    (ψ.hom ∘ b) ∈ groupCohomology.levelCoboundaries₂ r C ↔
      ∃ a ∈ groupCohomology.levelCocycles₂ r A, (b - φ.hom ∘ a) ∈ groupCohomology.levelCoboundaries₂ r B := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_comp_mem_levelCoboundaries2_iff_exists_levelCocycles2_sub_comp.solution
