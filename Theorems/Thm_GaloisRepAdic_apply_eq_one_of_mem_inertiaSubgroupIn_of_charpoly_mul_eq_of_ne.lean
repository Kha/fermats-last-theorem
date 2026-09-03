import Definitions.Def_GaloisRep_Adic
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_apply_eq_one_of_mem_inertiaSubgroupIn_of_charpoly_mul_eq_of_ne
attribute [-instance] GaloisRep.DeformationRingData.instIsLocalHom GaloisRep.DeformationRingData.instCommRing GaloisRep.DeformationRingData.instIsLocalRing GaloisRep.DeformationRingData.instIsNoetherianRing GaloisRep.DeformationRingData.instIsAdicComplete GaloisRep.DeformationRingData.instAlgebra
attribute [-simp] GaloisRep.DeformationRingData.mk.injEq GaloisRep.DeformationRingData.mk.sizeOf_spec

set_option autoImplicit false
open IsLocalRing Polynomial

theorem GaloisRepAdic.apply_eq_one_of_mem_inertiaSubgroupIn_of_charpoly_mul_eq_of_ne
    {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [CharZero O]
    (ρ : GaloisRepAdic O) {p : ℕ} (hp : p.Prime) (hpO : (p : O) ∈ maximalIdeal O)
    {q : ℕ} (hq : q.Prime) (hpq : p ≠ q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (hcp : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      LinearMap.charpoly (ρ.ρ (σ * g)) = LinearMap.charpoly (ρ.ρ g))
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : P.IsFrobeniusAt τ q)
    (hne : (q : O) * LinearMap.trace O ρ.V (ρ.ρ τ) ^ 2 ≠ ((q : O) + 1) ^ 2 * LinearMap.det (ρ.ρ τ)) :
    ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ σ = 1 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_apply_eq_one_of_mem_inertiaSubgroupIn_of_charpoly_mul_eq_of_ne.solution
