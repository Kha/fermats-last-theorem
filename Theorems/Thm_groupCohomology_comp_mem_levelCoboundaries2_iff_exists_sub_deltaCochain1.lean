import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import P2M.Util
import P2M.Sol.S_groupCohomology_comp_mem_levelCoboundaries2_iff_exists_sub_deltaCochain1

set_option autoImplicit false

universe u

open CategoryTheory
theorem groupCohomology.comp_mem_levelCoboundaries2_iff_exists_sub_deltaCochain1 {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) {A B C : Rep.{u} k G} (φ : A ⟶ B) (ψ : B ⟶ C)
    (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom) (hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b)
    (a : G × G → A) :
    (φ.hom ∘ a) ∈ groupCohomology.levelCoboundaries₂ r B ↔
      ∃ c : groupCohomology.cocycles₁ C, groupCohomology.IsLevelConstant₁ r c ∧
        (a - groupCohomology.deltaCochain₁ φ ψ hψ c) ∈ groupCohomology.levelCoboundaries₂ r A := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_comp_mem_levelCoboundaries2_iff_exists_sub_deltaCochain1.solution
