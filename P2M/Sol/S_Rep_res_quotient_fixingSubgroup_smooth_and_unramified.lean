import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
namespace P2MW.S_Rep_res_quotient_fixingSubgroup_smooth_and_unramified

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory Module groupCohomology ExtCitation

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hL : L.IsUnramifiedOutside S) [hn : L.fixingSubgroup.Normal]
    (X : Rep.{0} (ZMod p) ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ L.fixingSubgroup)) :
    (∀ m : Rep.res (QuotientGroup.mk' L.fixingSubgroup) X, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
        FiniteDimensional ℚ F ∧ ∀ s ∈ F.fixingSubgroup, (Rep.res (QuotientGroup.mk' L.fixingSubgroup) X).ρ s m = m) ∧
    (∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
        A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, (Rep.res (QuotientGroup.mk' L.fixingSubgroup) X).ρ g = 1) := by
  haveI := hL.1
  have key : ∀ s ∈ L.fixingSubgroup, (Rep.res (QuotientGroup.mk' L.fixingSubgroup) X).ρ s = 1 := fun s hs => by
    show X.ρ (QuotientGroup.mk' L.fixingSubgroup s) = 1
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff s).2 hs, map_one]
  refine ⟨fun m => ⟨L, hL.1, fun s hs => ?_⟩, fun q hq A hA g hg => key g (hL.2 q hq A hA hg)⟩
  rw [key s hs]
  rfl
