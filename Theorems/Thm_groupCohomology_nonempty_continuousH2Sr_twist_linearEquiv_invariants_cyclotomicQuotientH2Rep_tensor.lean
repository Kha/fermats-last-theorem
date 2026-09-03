import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_Rep_QuotientRightTranslation
import Definitions.Def_GroupCohomology_CyclotomicQuotientH2Rep
import P2M.Util
import P2M.Sol.S_groupCohomology_nonempty_continuousH2Sr_twist_linearEquiv_invariants_cyclotomicQuotientH2Rep_tensor

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module Limits groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith TensorProduct

theorem groupCohomology.nonempty_continuousH2Sr_twist_linearEquiv_invariants_cyclotomicQuotientH2Rep_tensor
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex]
    (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p)
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
    (htriv : ∀ s : ↥K.fixingSubgroup, (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ L.fixingSubgroup → N.ρ s = 1) :
    Nonempty (continuousH2Sr K.fixingSubgroup.subtype S (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)) ≃ₗ[ZMod p]
      (cyclotomicQuotientH2Rep S K L p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_nonempty_continuousH2Sr_twist_linearEquiv_invariants_cyclotomicQuotientH2Rep_tensor.solution
