import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_forall_algEquiv_laurentBaseChange_apply_eq_iff_mem_laurentBaseChange_of_fixedField

set_option autoImplicit false

theorem ModularCurve.forall_algEquiv_laurentBaseChange_apply_eq_iff_mem_laurentBaseChange_of_fixedField
    (L : Type) [Field L] [CharZero L]
    (F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)) (hle₁ : F₁ ≤ F₀)
    (G : Type) [Group G] [Finite G] (δ : G →* (↥F₀ ≃ₐ[ℚ] ↥F₀))
    (hF₁ : ∀ y : ↥F₀, (y : LaurentSeries ℚ) ∈ F₁ ↔ ∀ g : G, δ g y = y)
    (δL : G →* (↥(ModularCurve.laurentBaseChange L F₀) ≃ₐ[L] ↥(ModularCurve.laurentBaseChange L F₀)))
    (hδL : ∀ (g : G) (y : ↥F₀) (hy : ModularCurve.coeffEmb L (y : LaurentSeries ℚ) ∈ ModularCurve.laurentBaseChange L F₀),
      ((δL g ⟨ModularCurve.coeffEmb L (y : LaurentSeries ℚ), hy⟩ : ↥(ModularCurve.laurentBaseChange L F₀)) : LaurentSeries L) =
        ModularCurve.coeffEmb L ((δ g y : ↥F₀) : LaurentSeries ℚ))
    (x : ↥(ModularCurve.laurentBaseChange L F₀)) :
    (∀ g : G, δL g x = x) ↔ (x : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L F₁ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_forall_algEquiv_laurentBaseChange_apply_eq_iff_mem_laurentBaseChange_of_fixedField.solution
