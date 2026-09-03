import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import P2M.Util
import P2M.Sol.S_NumberField_ae_exists_mk_mul_out_mem_and_measure_inter_eq_zero_preimage_unitsAct_mul_inv_of_isFundamentalDomain_subgroupOf
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal

theorem NumberField.ae_exists_mk_mul_out_mem_and_measure_inter_eq_zero_preimage_unitsAct_mul_inv_of_isFundamentalDomain_subgroupOf
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]

    (AK : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hAKc : IsClosed (AK : Set (AdeleRing (𝓞 L) L)ˣ))
    (hAK : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a)
    (μAK : Measure AK) [μAK.IsHaarMeasure]

    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure]
    (cN : ℝ) (hcN : 0 < cN)
    (hNc : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ n : N1, g (n : (AdeleRing (𝓞 L) L)ˣ) ∂μN =
        cN * ∫ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
          g (D.unitsAct σ q.out * (q.out)⁻¹) ∂(HaarQuotient.measure νZL AK μAK))

    (Θ₁ : Set N1)
    (hΘ₁ : IsFundamentalDomain
      ((((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range).subgroupOf N1) Θ₁ μN) :
    NullMeasurableSet {q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ | D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' Θ₁ : Set (AdeleRing (𝓞 L) L)ˣ)}
      (HaarQuotient.measure νZL AK μAK) ∧
    (∀ᵐ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ ∂(HaarQuotient.measure νZL AK μAK), ∃ w : Lˣ,
      (Quotient.mk'' ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) w * q.out) : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) ∈
        {q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ | D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' Θ₁ : Set (AdeleRing (𝓞 L) L)ˣ)}) ∧
    (∀ w w' : Lˣ, w⁻¹ * w' ∉ Set.range (Units.map (algebraMap K L : K →* L)) →
      HaarQuotient.measure νZL AK μAK
        ({q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ |
          (Quotient.mk'' (((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) w)⁻¹ * q.out) : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) ∈
            {q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ | D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' Θ₁ : Set (AdeleRing (𝓞 L) L)ˣ)}} ∩
         {q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ |
          (Quotient.mk'' (((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) w')⁻¹ * q.out) : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) ∈
            {q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ | D.unitsAct σ q.out * (q.out)⁻¹ ∈ (Subtype.val '' Θ₁ : Set (AdeleRing (𝓞 L) L)ˣ)}}) = 0) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_ae_exists_mk_mul_out_mem_and_measure_inter_eq_zero_preimage_unitsAct_mul_inv_of_isFundamentalDomain_subgroupOf.solution
