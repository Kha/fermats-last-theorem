import Mathlib
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_ConditionLifts
import Definitions.Def_Deformations_ConjQuotSubfunctor
import Definitions.Def_Representation_AbsolutelyIrreducible
import Definitions.Def_Deformations_MatrixRepresentation
import P2M.Util
import P2M.Sol.S_GaloisRep_exists_algHom_baseChangeAlong_isEquiv_of_corepresentableBy
attribute [-instance] Deformation.ProartinianCat.instFiniteResidueField Deformation.ProartinianCat.instCompactSpace

set_option autoImplicit false
open CategoryTheory IsLocalRing
theorem GaloisRep.exists_algHom_baseChangeAlong_isEquiv_of_corepresentableBy
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] [Finite (ResidueField 𝒪)]
    (ρbar : ResidualGaloisRep (ResidueField 𝒪))
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (h𝒟 : GaloisRep.IsDeformationCondition 𝒪 𝒟)
    (ρ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) (Deformation.ProartinianCat.residueField (𝓞 := 𝒪)))
    (b : Module.Basis (Fin 2) (ResidueField 𝒪) ρbar.V)
    (hρ₀ : ∀ σ, (ρ₀ σ).val = LinearMap.toMatrix b b (ρbar.ρ σ))
    {R : Deformation.ProartinianCat 𝒪} [IsLocalRing.IsAdicTopology R]
    (e : (Deformation.conjQuotSubfunctor (Fin 2) (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀)).toFunctor.CorepresentableBy R)
    (ρu : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) R)
    (hρu : ρu ∈ (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀).obj R)
    (hρu' : (Quotient.mk'' ρu : (Deformation.repnQuotFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj R) = (e.homEquiv (𝟙 R)).1)
    (hcont : GaloisActionIsAdicContinuous R
      ((Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρu.toMonoidHom)))
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A]
    [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    (hresA : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A))
    (ρA : GaloisRepAdic A) (hDA : 𝒟 ρA)
    (hresEq : ρA.residual.IsEquiv (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 A)))) :
    ∃ φ : R →ₐ[𝒪] A, ∃ hφ : IsLocalHom (φ : R →+* A),
      (GaloisRepAdic.baseChangeAlong (φ : R →+* A) hφ
        { V := Fin 2 → R, finrank_eq := by simp,
          ρ := (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρu.toMonoidHom),
          isAdicContinuous := hcont }).IsEquiv ρA := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_exists_algHom_baseChangeAlong_isEquiv_of_corepresentableBy.solution
