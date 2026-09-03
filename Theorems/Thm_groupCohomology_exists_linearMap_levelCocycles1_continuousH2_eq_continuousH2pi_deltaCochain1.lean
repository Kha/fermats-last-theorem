import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_linearMap_levelCocycles1_continuousH2_eq_continuousH2pi_deltaCochain1

set_option autoImplicit false

universe u

open CategoryTheory
theorem groupCohomology.exists_linearMap_levelCocycles1_continuousH2_eq_continuousH2pi_deltaCochain1 {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) {A B C : Rep.{u} k G} (φ : A ⟶ B) (ψ : B ⟶ C)
    (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom) (hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b)
    (hsm : ∀ m : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → B.ρ s m = m) :
    ∃ δ : groupCohomology.levelCocycles₁ r C →ₗ[k] groupCohomology.continuousH2 r A,
      ∀ c : groupCohomology.levelCocycles₁ r C,
        ∃ h : groupCohomology.deltaCochain₁ φ ψ hψ ((c : groupCohomology.cocycles₁ C) : G → C)
            ∈ groupCohomology.levelCocycles₂ r A,
          δ c = groupCohomology.continuousH2π r A ⟨_, h⟩ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_linearMap_levelCocycles1_continuousH2_eq_continuousH2pi_deltaCochain1.solution
