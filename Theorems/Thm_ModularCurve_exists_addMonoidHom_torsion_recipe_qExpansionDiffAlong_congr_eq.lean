import Mathlib
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_ModularCurve_QExpansionDiff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_addMonoidHom_torsion_recipe_qExpansionDiffAlong_congr_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_addMonoidHom_torsion_recipe_qExpansionDiffAlong_congr_eq
    (K : Type*) [Field K] (p : ℕ)
    {F₁ F₂ : IntermediateField K (LaurentSeries K)} (hE : F₁ = F₂)
    (δ₁ : Pic0.torsion K F₁ p →+ Ω[↥F₁⁄K])
    (hδ₁ : ∀ (y : Pic0.torsion K F₁ p) (E : Divisor.degZero (K := K) (F := ↥F₁)) (g : ↥F₁),
        Pic0.mk E = (y : Pic0 K F₁) → g ≠ 0 →
        (∀ v : Place K F₁, (p : ℤ) * (E : Divisor K F₁) v = v.ord g) →
        δ₁ y = g⁻¹ • KaehlerDifferential.D K (↥F₁) g) :
    ∃ (τ : Pic0.torsion K F₁ p ≃+ Pic0.torsion K F₂ p)
      (δ₂ : Pic0.torsion K F₂ p →+ Ω[↥F₂⁄K]),
      (∀ x : Pic0.torsion K F₁ p, ((τ x : Pic0.torsion K F₂ p) : Pic0 K F₂) =
        Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
          (fun a => (IntermediateField.equivOfEq hE).commutes a) (x : Pic0 K F₁)) ∧
      (∀ (y : Pic0.torsion K F₂ p) (E : Divisor.degZero (K := K) (F := ↥F₂)) (g : ↥F₂),
        Pic0.mk E = (y : Pic0 K F₂) → g ≠ 0 →
        (∀ v : Place K F₂, (p : ℤ) * (E : Divisor K F₂) v = v.ord g) →
        δ₂ y = g⁻¹ • KaehlerDifferential.D K (↥F₂) g) ∧
      (∀ x : Pic0.torsion K F₁ p,
        qExpansionDiffAlong F₂.val (δ₂ (τ x)) = qExpansionDiffAlong F₁.val (δ₁ x)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_addMonoidHom_torsion_recipe_qExpansionDiffAlong_congr_eq.solution
