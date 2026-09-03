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
import P2M.Sol.S_PadicAlgCl_finrank_span_addChar_inertia_eq_zero_finiteLevel_le_one
attribute [-instance] instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem PadicAlgCl.finrank_span_addChar_inertia_eq_zero_finiteLevel_le_one
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] :
    FiniteDimensional k (Submodule.span k
        {φ : primeLocalGaloisGroup (pPrime p) → k |
          (∀ σ τ : primeLocalGaloisGroup (pPrime p), φ (σ * τ) = φ σ + φ τ) ∧
          (∀ σ : primeLocalGaloisGroup (pPrime p),
            ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → φ σ = 0) ∧
          ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
            ∀ (g s : primeLocalGaloisGroup (pPrime p)),
              primeLocalToGlobal (pPrime p) s ∈ F.fixingSubgroup → φ (g * s) = φ g}) ∧
      Module.finrank k (Submodule.span k
        {φ : primeLocalGaloisGroup (pPrime p) → k |
          (∀ σ τ : primeLocalGaloisGroup (pPrime p), φ (σ * τ) = φ σ + φ τ) ∧
          (∀ σ : primeLocalGaloisGroup (pPrime p),
            ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → φ σ = 0) ∧
          ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
            ∀ (g s : primeLocalGaloisGroup (pPrime p)),
              primeLocalToGlobal (pPrime p) s ∈ F.fixingSubgroup → φ (g * s) = φ g}) ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_finrank_span_addChar_inertia_eq_zero_finiteLevel_le_one.solution
