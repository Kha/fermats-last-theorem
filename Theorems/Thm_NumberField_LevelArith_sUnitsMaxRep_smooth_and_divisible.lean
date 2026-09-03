import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_SUnitsMax
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_sUnitsMaxRep_smooth_and_divisible

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField NumberField.LevelArith TensorProduct Pointwise

theorem NumberField.LevelArith.sUnitsMaxRep_smooth_and_divisible
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    (∀ a : sUnitsMaxRep S L, IsLevelConstantSr₁ L.fixingSubgroup.subtype S (fun g : ↥L.fixingSubgroup => (sUnitsMaxRep S L).ρ g a)) ∧
      ∀ x : sUnitsMaxRep S L, ∃ y : sUnitsMaxRep S L, (p : ℤ) • y = x := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_sUnitsMaxRep_smooth_and_divisible.solution
