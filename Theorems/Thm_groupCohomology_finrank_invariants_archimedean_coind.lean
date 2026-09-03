import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_invariants_archimedean_coind

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation
open scoped Classical

theorem groupCohomology.finrank_invariants_archimedean_coind
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N] :
    Module.finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inl ())) (Rep.coind K.fixingSubgroup.subtype N)).ρ.invariants =
      ∑ᶠ v : Quotient (MulAction.orbitRel ↥K.fixingSubgroup
          ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (extArithLoc S (Sum.inl ())).range)),
        Module.finrank (ZMod p) (Rep.res (MulAction.stabilizer (↥K.fixingSubgroup) v.out).subtype N).ρ.invariants := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_invariants_archimedean_coind.solution
