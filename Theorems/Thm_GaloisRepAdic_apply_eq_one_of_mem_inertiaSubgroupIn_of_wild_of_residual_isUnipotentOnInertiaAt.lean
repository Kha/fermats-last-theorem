import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_apply_eq_one_of_mem_inertiaSubgroupIn_of_wild_of_residual_isUnipotentOnInertiaAt

set_option autoImplicit false
open IsLocalRing Polynomial

theorem GaloisRepAdic.apply_eq_one_of_mem_inertiaSubgroupIn_of_wild_of_residual_isUnipotentOnInertiaAt
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (ρ : GaloisRepAdic R) {p : ℕ} (hp : p.Prime) (hpR : (p : R) ∈ maximalIdeal R) {q : ℕ} (hq : q.Prime)
    (hqp : q ≠ p)
    (hres : (GaloisRepAdic.ofResidualGaloisRep ρ.residual).IsUnipotentOnInertiaAt q)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hP : P.LiesOverPrime q) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ)
    (hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) :
    ρ.ρ σ = 1 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_apply_eq_one_of_mem_inertiaSubgroupIn_of_wild_of_residual_isUnipotentOnInertiaAt.solution
