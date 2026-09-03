import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_GaloisRep_OrdinaryUnitClasses
import P2M.Util
import P2M.Sol.S_ExtCitation_exists_finiteDimensional_fixingSubgroup_comap_primeLocalToGlobal_le

set_option autoImplicit false

p2m_open "CategoryTheory groupCohomology TrivSqZeroExt ExtCitation~forall_exists_finiteDimensional_primeLocalToGlobal_iff"

theorem ExtCitation.exists_finiteDimensional_fixingSubgroup_comap_primeLocalToGlobal_le
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : primeLocalGaloisGroup (pPrime p), primeLocalToGlobal (pPrime p) s ∈ F.fixingSubgroup →
        ∀ x ∈ K, ResidualGaloisRep.localAut p s x = x := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_exists_finiteDimensional_fixingSubgroup_comap_primeLocalToGlobal_le.solution
