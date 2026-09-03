import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_det_eq_one_of_mem_inertiaSubgroupIn
attribute [-instance] GaloisRep.DeformationRingData.instIsLocalHom GaloisRep.DeformationRingData.instCommRing GaloisRep.DeformationRingData.instIsLocalRing GaloisRep.DeformationRingData.instIsNoetherianRing GaloisRep.DeformationRingData.instIsAdicComplete GaloisRep.DeformationRingData.instAlgebra
attribute [-simp] GaloisRep.DeformationRingData.mk.injEq GaloisRep.DeformationRingData.mk.sizeOf_spec

theorem GaloisRepAdic.det_eq_one_of_mem_inertiaSubgroupIn
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (ρ : GaloisRepAdic A) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hdet : ρ.DetIsCyclotomic p) (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    LinearMap.det (ρ.ρ τ) = 1 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_det_eq_one_of_mem_inertiaSubgroupIn.solution
