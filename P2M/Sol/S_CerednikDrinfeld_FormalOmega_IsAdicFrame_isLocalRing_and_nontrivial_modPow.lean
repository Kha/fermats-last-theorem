import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_isLocalRing_and_nontrivial_modPow

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀] {π : 𝒪}
    {C : Type} [Field C] [Algebra K₀ C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K₀ C]
    (ϖ : PseudoUniformizer K₀ C) (hF : IsAdicFrame π ϖ R) :
    IsLocalRing R ∧ Nontrivial (modPow π R 0) := by
  have hinj := hF.injective
  haveI : Nontrivial R := ⟨⟨0, 1, fun h => zero_ne_one (by rw [← map_zero (algebraMap R C), h, map_one])⟩⟩

  have hunit : ∀ a : R, Valued.v (algebraMap R C a) = 1 → IsUnit a := by
    intro a ha
    have ha0 : algebraMap R C a ≠ 0 := by
      intro h; rw [h, Valued.v.map_zero] at ha; exact zero_ne_one ha
    obtain ⟨b, hb⟩ := (hF.range_eq (algebraMap R C a)⁻¹).1 (by rw [map_inv₀, ha, inv_one])
    refine IsUnit.of_mul_eq_one b (hinj ?_)
    rw [map_mul, hb, mul_inv_cancel₀ ha0, map_one]
  constructor
  · refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
    by_cases ha : Valued.v (algebraMap R C a) = 1
    · exact Or.inl (hunit a ha)
    · right
      apply hunit
      have hlt : Valued.v (algebraMap R C a) < 1 := lt_of_le_of_ne (hF.v_algebraMap_le_one a) ha
      rw [map_sub, map_one]
      exact Valuation.map_one_sub_of_lt _ hlt
  ·
    have hπ : ¬ IsUnit (algebraMap 𝒪 R π ^ (0 + 1)) := by
      rw [zero_add, pow_one]
      intro hu
      obtain ⟨u, hu⟩ := hu
      have h1 : Valued.v (algebraMap R C (algebraMap 𝒪 R π)) < 1 := by
        rw [← IsScalarTower.algebraMap_apply]; exact hF.v_algebraMap_lt_one
      have h2 : Valued.v (algebraMap R C (algebraMap 𝒪 R π)) * Valued.v (algebraMap R C ↑u⁻¹) = 1 := by
        rw [← map_mul, ← map_mul, ← hu, Units.mul_inv, map_one, map_one]
      have h3 := hF.v_algebraMap_le_one (↑u⁻¹ : R)
      have : Valued.v (algebraMap R C (algebraMap 𝒪 R π)) * Valued.v (algebraMap R C ↑u⁻¹) < 1 * 1 :=
        mul_lt_mul_of_lt_of_le_of_nonneg_of_pos h1 h3 zero_le' ?_
      · rw [one_mul] at this; exact absurd h2 (ne_of_lt this)
      ·
        exact zero_lt_one
    exact Ideal.Quotient.nontrivial_iff.2 (by rw [Ne, Ideal.span_singleton_eq_top]; exact hπ)
