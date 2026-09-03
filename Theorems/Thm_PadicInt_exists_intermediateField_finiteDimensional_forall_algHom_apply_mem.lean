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
import P2M.Sol.S_PadicInt_exists_intermediateField_finiteDimensional_forall_algHom_apply_mem

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem PadicInt.exists_intermediateField_finiteDimensional_forall_algHom_apply_mem
    (p : ℕ) [Fact p.Prime] (H : Type) [CommRing H] [Algebra ℤ_[p] H] [Module.Finite ℤ_[p] H] :
    ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] L ∧
      ∀ (f : H →ₐ[ℤ_[p]] PadicAlgCl p) (h : H), f h ∈ L := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_exists_intermediateField_finiteDimensional_forall_algHom_apply_mem.solution
