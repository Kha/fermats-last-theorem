import Definitions.Def_GaloisRep_Adic
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt
attribute [-instance] GaloisRep.DeformationRingData.instIsLocalHom GaloisRep.DeformationRingData.instCommRing GaloisRep.DeformationRingData.instIsLocalRing GaloisRep.DeformationRingData.instIsNoetherianRing GaloisRep.DeformationRingData.instIsAdicComplete GaloisRep.DeformationRingData.instAlgebra
attribute [-simp] GaloisRep.DeformationRingData.mk.injEq GaloisRep.DeformationRingData.mk.sizeOf_spec

theorem GaloisRepAdic.conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (ρ : GaloisRepAdic 𝒪) (q : ℕ)
    (hunip : ∀ P' : ValuationSubring (AlgebraicClosure ℚ), P'.LiesOverPrime q →
      ∀ τ ∈ P'.inertiaSubgroupIn ℚ, LinearMap.charpoly (ρ.ρ τ) = (Polynomial.X - 1) ^ 2)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (p : ℕ) (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (hdivI : ∀ (n : ℕ) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), τ ∈ P.inertiaSubgroupIn ℚ →
      ∃ w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, w ∈ P.inertiaSubgroupIn ℚ ∧
        w ^ (p ^ n) = σ * τ * σ⁻¹ * (τ ^ q)⁻¹)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    ρ.ρ σ * ρ.ρ τ * ρ.ρ σ⁻¹ = ρ.ρ τ ^ q := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.solution
