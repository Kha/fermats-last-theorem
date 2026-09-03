import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import P2M.Util
import P2M.Sol.S_GaloisRep_DeformationRingData_exists_generators_maximalIdeal_card_le_finrank_span_dualNumberClasses

set_option autoImplicit false

open IsLocalRing groupCohomology TrivSqZeroExt

theorem GaloisRep.DeformationRingData.exists_generators_maximalIdeal_card_le_finrank_span_dualNumberClasses
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    {ρbar : ResidualGaloisRep (ResidueField 𝒪)}
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p)
    {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟) (hdetR : D.ρ.DetIsCyclotomic p) :
    letI : Algebra 𝒪 (DualNumber (ResidueField 𝒪)) :=
      ((algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪))).comp
        (algebraMap 𝒪 (ResidueField 𝒪))).toAlgebra
    (∀ (φ : D.R →ₐ[𝒪] DualNumber (ResidueField 𝒪))
        (hφ : IsLocalHom (φ : D.R →+* DualNumber (ResidueField 𝒪))),
        𝒟 (D.ρ.baseChangeAlong (φ : D.R →+* DualNumber (ResidueField 𝒪)) hφ)) →
    ∃ (m : ℕ) (a : Fin m → D.R), (∀ i, a i ∈ maximalIdeal D.R) ∧
      maximalIdeal D.R ≤ Ideal.span (Set.range a) ⊔ maximalIdeal D.R ^ 2 ⊔
        (maximalIdeal 𝒪).map (algebraMap 𝒪 D.R) ∧
      m ≤ Module.finrank (ResidueField 𝒪) (Submodule.span (ResidueField 𝒪)
        {x : H1 ρbar.adZero |
          ∃ c : cocycles₁ ρbar.adZero, H1π ρbar.adZero c = x ∧
          ∃ ρA : GaloisRepAdic (DualNumber (ResidueField 𝒪)),
            𝒟 ρA ∧
          ∃ ρd : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
              (DualNumber (Module.End (ResidueField 𝒪) ρbar.V))ˣ,
            IsDualLift ρbar.ρ.toHomUnits ρd ∧
            (∀ σ, ((c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
                ↥(LinearMap.ker (LinearMap.trace (ResidueField 𝒪) ρbar.V))) σ :
                  Module.End (ResidueField 𝒪) ρbar.V) =
              dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) ∧
            ∃ (b : Module.Basis (Fin 2) (DualNumber (ResidueField 𝒪)) ρA.V)
              (bbar : Module.Basis (Fin 2) (ResidueField 𝒪) ρbar.V),
              ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
                Matrix.dualNumberEquiv.symm
                  ⟨LinearMap.toMatrix bbar bbar
                      ((ρd σ : DualNumber (Module.End (ResidueField 𝒪) ρbar.V)).fst),
                    LinearMap.toMatrix bbar bbar
                      ((ρd σ : DualNumber (Module.End (ResidueField 𝒪) ρbar.V)).snd)⟩}) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_DeformationRingData_exists_generators_maximalIdeal_card_le_finrank_span_dualNumberClasses.solution
