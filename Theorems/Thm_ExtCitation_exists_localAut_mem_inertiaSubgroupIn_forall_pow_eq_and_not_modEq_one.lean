import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ExtCitation_exists_localAut_mem_inertiaSubgroupIn_forall_pow_eq_and_not_modEq_one

set_option autoImplicit false

open ExtCitation

theorem ExtCitation.exists_localAut_mem_inertiaSubgroupIn_forall_pow_eq_and_not_modEq_one
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ σ : primeLocalGaloisGroup (pPrime p),
      ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] ∧
      ∃ c : ℕ, (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → ResidualGaloisRep.localAut p σ ζ = ζ ^ c) ∧
        (c : ZMod p) ≠ 1 := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_exists_localAut_mem_inertiaSubgroupIn_forall_pow_eq_and_not_modEq_one.solution
