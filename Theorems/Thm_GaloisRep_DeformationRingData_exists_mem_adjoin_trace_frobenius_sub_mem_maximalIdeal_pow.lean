import Definitions.Def_GaloisRep_DeformationRingData
import P2M.Util
import P2M.Sol.S_GaloisRep_DeformationRingData_exists_mem_adjoin_trace_frobenius_sub_mem_maximalIdeal_pow
attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

theorem GaloisRep.DeformationRingData.exists_mem_adjoin_trace_frobenius_sub_mem_maximalIdeal_pow
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟)
    (h𝒟 : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)],
        Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A) →
        ∀ (f : D.R →ₐ[𝒪] A) (hf : IsLocalHom (f : D.R →+* A)),
          𝒟 (D.ρ.baseChangeAlong (f : D.R →+* A) hf))
    (S : Finset ℕ) (n : ℕ) (x : D.R) :
    ∃ b ∈ Algebra.adjoin 𝒪 {y : D.R | ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ S ∧
        ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ ∧
          ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ ∧ y = D.ρ.trace σ},
      x - b ∈ IsLocalRing.maximalIdeal D.R ^ n := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_DeformationRingData_exists_mem_adjoin_trace_frobenius_sub_mem_maximalIdeal_pow.solution
