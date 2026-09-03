import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_isGalois_forall_mem_continuousH1S_exists_cocyclesOne

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.exists_isGalois_forall_mem_continuousH1S_exists_cocyclesOne
    {k : Type} [CommRing k] [Finite k] (S : Finset Nat.Primes) (M : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [Module.Finite k ↥(continuousH1S S M)] :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : NumberField ↥F) (_ : IsGalois ℚ ↥F), F.IsUnramifiedOutside S ∧
      ∀ x : H1 M, x ∈ continuousH1S S M →
        ∃ ny : cocycles₁ M, (H1π M).hom ny = x ∧
          (∀ (γ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F.fixingSubgroup → ny (γ * s) = ny γ) ∧
          (∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ F.fixingSubgroup → ny s = 0) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_isGalois_forall_mem_continuousH1S_exists_cocyclesOne.solution
