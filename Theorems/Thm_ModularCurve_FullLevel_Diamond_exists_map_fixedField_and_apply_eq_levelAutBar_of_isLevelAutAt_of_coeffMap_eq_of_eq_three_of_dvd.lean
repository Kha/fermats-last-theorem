import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_ArithmeticGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_Diamond_exists_map_fixedField_and_apply_eq_levelAutBar_of_isLevelAutAt_of_coeffMap_eq_of_eq_three_of_dvd
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups

theorem ModularCurve.FullLevel.Diamond.exists_map_fixedField_and_apply_eq_levelAutBar_of_isLevelAutAt_of_coeffMap_eq_of_eq_three_of_dvd
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ q)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK : K = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (G : Subgroup (↥K ≃ₐ[↥k₀] ↥K))
    (hG : G = Subgroup.closure {τ : ↥K ≃ₐ[↥k₀] ↥K | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧
      γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ K τ})
    (K₀ : IntermediateField ↥k₀ ↥K) (hK₀ : K₀ = IntermediateField.fixedField G) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),

      (∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ∃ c : ↥k₀,
        ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n = ((c : ↥k₀) : AlgebraicClosure ℚ)) →
    ∀ (φ : ↥K₀ ≃ₐ[↥k₀] ↥F₀),

      (∀ f : ↥K₀, coeffMap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) (((f : ↥K)) : LaurentSeries ↥k₀) =
        (                                ((φ f : ↥F₀) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))) →

      (∀ (ζ : Idx q) (ξ' : ↥k₀), IsPrimitiveRoot ξ' q → ζ.val = (((ξ' : ↥k₀)) : AlgebraicClosure ℚ) →
        ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ (τ : ↥K ≃ₐ[↥k₀] ↥K),
          ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ' q (q ^ 2 * M') H₁ γ K τ →
          ∃ hτ : ∀ f : ↥K, f ∈ K₀ → τ f ∈ K₀,
            ∀ f : ↥K₀, ((φ ⟨τ (f : ↥K), hτ (f : ↥K) f.2⟩ : ↥F₀) : ↥(fieldBar q M')) =
              levelAutBar q M' ζ γ ((φ f : ↥F₀) : ↥(fieldBar q M'))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_Diamond_exists_map_fixedField_and_apply_eq_levelAutBar_of_isLevelAutAt_of_coeffMap_eq_of_eq_three_of_dvd.solution
