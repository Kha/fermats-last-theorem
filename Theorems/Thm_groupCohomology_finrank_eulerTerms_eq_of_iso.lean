import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_eulerTerms_eq_of_iso

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation
theorem groupCohomology.finrank_eulerTerms_eq_of_iso
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M N : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (e : M ≅ N) :
    finrank (ZMod p) M.ρ.invariants = finrank (ZMod p) N.ρ.invariants ∧
    finrank (ZMod p) (continuousH1S S M) = finrank (ZMod p) (continuousH1S S N) ∧
    finrank (ZMod p) (continuousH2S S M) = finrank (ZMod p) (continuousH2S S N) ∧
    finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inl ())) M).ρ.invariants
      = finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inl ())) N).ρ.invariants ∧
    finrank (ZMod p) M = finrank (ZMod p) N := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_eulerTerms_eq_of_iso.solution
