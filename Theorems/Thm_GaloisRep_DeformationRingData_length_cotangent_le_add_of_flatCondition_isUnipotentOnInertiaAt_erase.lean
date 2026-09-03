import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv
import Definitions.Def_Algebra_PatchingDatum
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import P2M.Util
import P2M.Sol.S_GaloisRep_DeformationRingData_length_cotangent_le_add_of_flatCondition_isUnipotentOnInertiaAt_erase
attribute [-instance] instIsScalarTowerTensorProduct_definitions
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

open scoped Pointwise
theorem GaloisRep.DeformationRingData.length_cotangent_le_add_of_flatCondition_isUnipotentOnInertiaAt_erase
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) (S U : Finset ℕ) (hpS : p ∈ S) (hqS : q ∈ S) (hUS : U ⊆ S) (hqU : q ∈ U)
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar
      (fun ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρ : GaloisRepAdic A) =>
        GaloisRep.flatCondition 𝒪 p S ρ ∧ ∀ r ∈ U, r.Prime → r ≠ p → ρ.IsUnipotentOnInertiaAt r))
    (D' : GaloisRep.DeformationRingData 𝒪 ρbar
      (fun ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρ : GaloisRepAdic A) =>
        GaloisRep.flatCondition 𝒪 p S ρ ∧ ∀ r ∈ U, r.Prime → r ≠ p → r ≠ q → ρ.IsUnipotentOnInertiaAt r))
    (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
    (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪)) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (hθsurj : Function.Surjective (θ : D'.R →+* D₀.R))
    (hexP : ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q)
    (hexσ : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ q)
    (hconj : ∀ P P' : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q → P'.LiesOverPrime q →
      ∃ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, g • P = P') :
    Module.length 𝒪 (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent ≤
      Module.length 𝒪 (RingHom.ker x₀).Cotangent +
        Module.length 𝒪 (𝒪 ⧸ Ideal.span {(q : 𝒪) ^ 2 - 1}) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_DeformationRingData_length_cotangent_le_add_of_flatCondition_isUnipotentOnInertiaAt_erase.solution
