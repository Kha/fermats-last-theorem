import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_DualSelmer_ExtConditions
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_invariants_archimedean_add_dualTwist_add_H1_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation
theorem groupCohomology.finrank_invariants_archimedean_add_dualTwist_add_H1_eq
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M] :
    finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inl ())) M).ρ.invariants
      + finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inl ())) (M.dualTwist (cycloChar p))).ρ.invariants
      + finrank (ZMod p) (H1 (Rep.res (extArithLoc S (Sum.inl ())) M))
    = finrank (ZMod p) M
      + 2 * finrank (ZMod p)
          (continuousH2 (extArithLoc S (Sum.inl ())) (Rep.res (extArithLoc S (Sum.inl ())) M)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_invariants_archimedean_add_dualTwist_add_H1_eq.solution
