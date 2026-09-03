import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth

set_option autoImplicit false

open CategoryTheory

theorem groupCohomology.exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth (S : Finset Nat.Primes)
    {k : Type} [CommRing k] (M : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [Module.Finite k M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s = 1 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth.solution
