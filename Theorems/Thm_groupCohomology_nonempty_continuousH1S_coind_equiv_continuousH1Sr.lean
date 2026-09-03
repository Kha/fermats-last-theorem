import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import P2M.Util
import P2M.Sol.S_groupCohomology_nonempty_continuousH1S_coind_equiv_continuousH1Sr
attribute [-simp] groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology
theorem groupCohomology.nonempty_continuousH1S_coind_equiv_continuousH1Sr
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : K.IsUnramifiedOutside S)
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
    (hN : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ s : ↥K.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ F.fixingSubgroup → N.ρ s n = n) :
    Nonempty (continuousH1S S (Rep.coind K.fixingSubgroup.subtype N)
      ≃ₗ[ZMod p] continuousH1Sr K.fixingSubgroup.subtype S N) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_nonempty_continuousH1S_coind_equiv_continuousH1Sr.solution
