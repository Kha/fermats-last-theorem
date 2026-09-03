import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import P2M.Util
import P2M.Sol.S_groupCohomology_mem_continuousH1S_of_forall_map_primeLocalToGlobal_eq_zero

set_option autoImplicit false

open CategoryTheory groupCohomology ExtCitation

theorem groupCohomology.mem_continuousH1S_of_forall_map_primeLocalToGlobal_eq_zero
    {k : Type} [CommRing k] (S Q : Finset Nat.Primes)
    (M : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1)
    (x : H1 M) (hx : x ∈ continuousH1S (S ∪ Q) M)
    (h0 : ∀ q ∈ Q, (groupCohomology.map (primeLocalToGlobal q)
      (𝟙 (Rep.res (primeLocalToGlobal q) M)) 1).hom x = 0) :
    x ∈ continuousH1S S M := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_mem_continuousH1S_of_forall_map_primeLocalToGlobal_eq_zero.solution
