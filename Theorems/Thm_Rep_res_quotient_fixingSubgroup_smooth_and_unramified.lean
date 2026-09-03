import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
import P2M.Sol.S_Rep_res_quotient_fixingSubgroup_smooth_and_unramified

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation
theorem Rep.res_quotient_fixingSubgroup_smooth_and_unramified
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hL : L.IsUnramifiedOutside S) [hn : L.fixingSubgroup.Normal]
    (X : Rep.{0} (ZMod p) ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ L.fixingSubgroup)) :
    (∀ m : Rep.res (QuotientGroup.mk' L.fixingSubgroup) X, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
        FiniteDimensional ℚ F ∧ ∀ s ∈ F.fixingSubgroup, (Rep.res (QuotientGroup.mk' L.fixingSubgroup) X).ρ s m = m) ∧
    (∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
        A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, (Rep.res (QuotientGroup.mk' L.fixingSubgroup) X).ρ g = 1) := by p2m_exact_reverting @_root_.P2MW.S_Rep_res_quotient_fixingSubgroup_smooth_and_unramified.solution
