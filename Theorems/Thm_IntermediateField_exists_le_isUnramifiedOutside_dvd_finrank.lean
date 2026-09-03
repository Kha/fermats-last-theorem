import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import P2M.Util
import P2M.Sol.S_IntermediateField_exists_le_isUnramifiedOutside_dvd_finrank
attribute [-instance] WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand ExtCitation
open scoped Classical

theorem IntermediateField.exists_le_isUnramifiedOutside_dvd_finrank
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L'] (hL' : L'.IsUnramifiedOutside S) :
    ∃ (M : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : L' ≤ M),
      M.IsUnramifiedOutside S ∧ p ∣ Module.finrank ↥L' ↥(IntermediateField.extendScalars h) := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_exists_le_isUnramifiedOutside_dvd_finrank.solution
