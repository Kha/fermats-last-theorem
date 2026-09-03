import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import P2M.Util
import P2M.Sol.S_groupCohomology_deltaCochain1_mem_levelCocycles2

set_option autoImplicit false

universe u

open CategoryTheory
theorem groupCohomology.deltaCochain1_mem_levelCocycles2 {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) {A B C : Rep.{u} k G} (φ : A ⟶ B) (ψ : B ⟶ C)
    (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom) (hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b)
    (hsm : ∀ m : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → B.ρ s m = m)
    (c : groupCohomology.cocycles₁ C) (hc : groupCohomology.IsLevelConstant₁ r c) :
    groupCohomology.deltaCochain₁ φ ψ hψ c ∈ groupCohomology.levelCocycles₂ r A := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_deltaCochain1_mem_levelCocycles2.solution
