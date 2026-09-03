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
import P2M.Sol.S_NumberField_LevelArith_nonempty_repTorsionP_sUnitsMaxRep_iso_trivial_twist_cycloChar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField NumberField.LevelArith TensorProduct Pointwise

theorem NumberField.LevelArith.nonempty_repTorsionP_sUnitsMaxRep_iso_trivial_twist_cycloChar
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    Nonempty (repTorsionP p (sUnitsMaxRep S L) ≅
      (Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_nonempty_repTorsionP_sUnitsMaxRep_iso_trivial_twist_cycloChar.solution
