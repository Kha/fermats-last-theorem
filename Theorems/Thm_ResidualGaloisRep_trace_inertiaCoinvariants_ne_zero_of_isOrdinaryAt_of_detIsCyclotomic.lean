import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.LinearAlgebra.Trace
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_trace_inertiaCoinvariants_ne_zero_of_isOrdinaryAt_of_detIsCyclotomic

set_option autoImplicit false

theorem ResidualGaloisRep.trace_inertiaCoinvariants_ne_zero_of_isOrdinaryAt_of_detIsCyclotomic
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρbar : ResidualGaloisRep k)
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p)
    (hord : (GaloisRepAdic.ofResidualGaloisRep ρbar).IsOrdinaryAt p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (E : (ρbar.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)) →ₗ[k]
      (ρbar.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)))
    (hE : ∀ v : ρbar.V, E (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρbar.ρ σ v)) :
    LinearMap.trace k _ E ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_trace_inertiaCoinvariants_ne_zero_of_isOrdinaryAt_of_detIsCyclotomic.solution
