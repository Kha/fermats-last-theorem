import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_place_comap_algebraMap_eq_of_finite
attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_place_comap_algebraMap_eq_of_finite
    (κ : Type) [Field κ] [IsAlgClosed κ]
    (Ω : Type) [Field Ω] [Algebra κ Ω] (V : Place κ Ω)
    (res : IsLocalRing.ResidueField ↥V.toValuationSubring →+* κ)
    (hr : ∀ c : κ, res (algebraMap κ (IsLocalRing.ResidueField ↥V.toValuationSubring) c) = c)
    (x : Ω) (hx : Transcendental κ x) [FiniteDimensional ↥(IntermediateField.adjoin κ ({x} : Set Ω)) Ω]
    (Ω₁ : Type) [Field Ω₁] [Algebra κ Ω₁] [Algebra Ω Ω₁] [IsScalarTower κ Ω Ω₁] [Module.Finite Ω Ω₁] :
    ∃ (V₁ : Place κ Ω₁) (res₁ : IsLocalRing.ResidueField ↥V₁.toValuationSubring →+* κ)
      (ιO : ↥V.toValuationSubring →+* ↥V₁.toValuationSubring),
      V₁.toValuationSubring.comap (algebraMap Ω Ω₁) = V.toValuationSubring ∧
      (∀ a : ↥V.toValuationSubring, ((ιO a : ↥V₁.toValuationSubring) : Ω₁) = algebraMap Ω Ω₁ (a : Ω)) ∧
      (∀ c : κ, res₁ (algebraMap κ (IsLocalRing.ResidueField ↥V₁.toValuationSubring) c) = c) ∧
      (∀ a : ↥V.toValuationSubring,
        res₁ (IsLocalRing.residue ↥V₁.toValuationSubring (ιO a)) = res (IsLocalRing.residue ↥V.toValuationSubring a)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_place_comap_algebraMap_eq_of_finite.solution
