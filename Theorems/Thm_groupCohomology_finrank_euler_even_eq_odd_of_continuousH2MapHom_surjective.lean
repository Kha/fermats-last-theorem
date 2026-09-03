import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_euler_even_eq_odd_of_continuousH2MapHom_surjective

set_option autoImplicit false

universe u

open CategoryTheory
theorem groupCohomology.finrank_euler_even_eq_odd_of_continuousH2MapHom_surjective {k G : Type u} [Field k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) {A B C : Rep.{u} k G} (φ : A ⟶ B) (ψ : B ⟶ C)
    (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom) (hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b)
    (hsm : ∀ m : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → B.ρ s m = m)
    [FiniteDimensional k A.ρ.invariants] [FiniteDimensional k C.ρ.invariants]
    [FiniteDimensional k (groupCohomology.continuousH1 r A)] [FiniteDimensional k (groupCohomology.continuousH1 r C)]
    [FiniteDimensional k (groupCohomology.continuousH2 r A)] [FiniteDimensional k (groupCohomology.continuousH2 r C)]
    (hsurj : Function.Surjective (groupCohomology.continuousH2MapHom r ψ)) :
    Module.finrank k A.ρ.invariants + Module.finrank k C.ρ.invariants
        + Module.finrank k (groupCohomology.continuousH1 r B)
        + Module.finrank k (groupCohomology.continuousH2 r A) + Module.finrank k (groupCohomology.continuousH2 r C)
      = Module.finrank k B.ρ.invariants
        + Module.finrank k (groupCohomology.continuousH1 r A) + Module.finrank k (groupCohomology.continuousH1 r C)
        + Module.finrank k (groupCohomology.continuousH2 r B) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_euler_even_eq_odd_of_continuousH2MapHom_surjective.solution
