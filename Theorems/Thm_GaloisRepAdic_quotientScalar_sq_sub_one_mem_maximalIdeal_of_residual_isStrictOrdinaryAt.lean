import Mathlib
import Definitions.Def_GaloisRep_StrictOrdinary
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_quotientScalar_sq_sub_one_mem_maximalIdeal_of_residual_isStrictOrdinaryAt

set_option autoImplicit false
theorem GaloisRepAdic.quotientScalar_sq_sub_one_mem_maximalIdeal_of_residual_isStrictOrdinaryAt
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hdet : ρ.DetIsCyclotomic p)
    (hstrbar : (GaloisRepAdic.ofResidualGaloisRep ρ.residual).IsStrictOrdinaryAt p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (L : Submodule A ρ.V) (hLb : ∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0)
    (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.decompositionSubgroup ℚ)
    (z : A) (hz : ∀ v : ρ.V, ρ.ρ σ v - z • v ∈ L) :
    z * z - 1 ∈ IsLocalRing.maximalIdeal A := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_quotientScalar_sq_sub_one_mem_maximalIdeal_of_residual_isStrictOrdinaryAt.solution
