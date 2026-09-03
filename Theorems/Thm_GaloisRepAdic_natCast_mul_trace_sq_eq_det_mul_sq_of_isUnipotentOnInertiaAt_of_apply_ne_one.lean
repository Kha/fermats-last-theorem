import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_natCast_mul_trace_sq_eq_det_mul_sq_of_isUnipotentOnInertiaAt_of_apply_ne_one
attribute [-instance] GaloisRep.DeformationRingData.instIsLocalHom GaloisRep.DeformationRingData.instCommRing GaloisRep.DeformationRingData.instIsLocalRing GaloisRep.DeformationRingData.instIsNoetherianRing GaloisRep.DeformationRingData.instIsAdicComplete GaloisRep.DeformationRingData.instAlgebra
attribute [-simp] GaloisRep.DeformationRingData.mk.injEq GaloisRep.DeformationRingData.mk.sizeOf_spec

set_option autoImplicit false
open Polynomial

theorem GaloisRepAdic.natCast_mul_trace_sq_eq_det_mul_sq_of_isUnipotentOnInertiaAt_of_apply_ne_one
    {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (ρ : GaloisRepAdic A)
    {p : ℕ} (hp : p.Prime) (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A) {q : ℕ} (hq : q.Prime)
    (hqp : q ≠ p)
    (hunip : ρ.IsUnipotentOnInertiaAt q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (hram : ∃ τ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ τ ≠ 1)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : P.IsFrobeniusAt σ q) :
    (q : A) * ρ.trace σ ^ 2 = LinearMap.det (ρ.ρ σ) * ((q : A) + 1) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_natCast_mul_trace_sq_eq_det_mul_sq_of_isUnipotentOnInertiaAt_of_apply_ne_one.solution
