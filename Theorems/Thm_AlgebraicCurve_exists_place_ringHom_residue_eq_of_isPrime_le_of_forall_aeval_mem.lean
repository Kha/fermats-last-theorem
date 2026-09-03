import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_place_ringHom_residue_eq_of_isPrime_le_of_forall_aeval_mem
attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_place_ringHom_residue_eq_of_isPrime_le_of_forall_aeval_mem
    (A₀ : Type) [CommRing A₀] [IsLocalRing A₀]
    (κ : Type) [Field κ] [IsAlgClosed κ]
    (θ : IsLocalRing.ResidueField A₀ →+* κ) (hθ : Function.Bijective θ)
    (C : Type) [CommRing C] [IsDomain C] [Algebra A₀ C] (j : C)
    (hfin : Module.Finite ↥(Algebra.adjoin A₀ ({j} : Set C)) C)
    (y : Ideal C) (hy : y.IsMaximal)
    (ψ : C →ₐ[A₀] IsLocalRing.ResidueField A₀) (hψ : ∀ c : C, ψ c = 0 ↔ c ∈ y)
    (𝔭 : Ideal C) (h𝔭 : 𝔭.IsPrime) (h𝔭y : 𝔭 ≤ y) (h𝔭ne : 𝔭 ≠ y)
    (h𝔪 : ∀ a ∈ IsLocalRing.maximalIdeal A₀, algebraMap A₀ C a ∈ 𝔭)
    (ht : ∀ f : Polynomial A₀, Polynomial.aeval j f ∈ 𝔭 → ∀ i : ℕ, f.coeff i ∈ IsLocalRing.maximalIdeal A₀) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : DecidableEq Ω) (_ : Algebra κ Ω)
      (V : Place κ Ω)
      (res : IsLocalRing.ResidueField ↥V.toValuationSubring →+* κ)
      (ρ : C →+* ↥V.toValuationSubring),
      (∀ c : κ, res (algebraMap κ (IsLocalRing.ResidueField ↥V.toValuationSubring) c) = c) ∧
      (∀ a : A₀, ((ρ (algebraMap A₀ C a) : ↥V.toValuationSubring) : Ω) =
        algebraMap κ Ω (θ (IsLocalRing.residue A₀ a))) ∧
      (∀ c : C, res (IsLocalRing.residue ↥V.toValuationSubring (ρ c)) = θ (ψ c)) ∧
      Transcendental κ ((ρ j : ↥V.toValuationSubring) : Ω) ∧
      FiniteDimensional ↥(IntermediateField.adjoin κ ({((ρ j : ↥V.toValuationSubring) : Ω)} : Set Ω)) Ω ∧
      (∀ c : C, ((ρ c : ↥V.toValuationSubring) : Ω) = 0 ↔ c ∈ 𝔭) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_place_ringHom_residue_eq_of_isPrime_le_of_forall_aeval_mem.solution
