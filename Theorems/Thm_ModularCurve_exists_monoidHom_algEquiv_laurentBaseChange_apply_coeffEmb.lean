import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_monoidHom_algEquiv_laurentBaseChange_apply_coeffEmb

set_option autoImplicit false

theorem ModularCurve.exists_monoidHom_algEquiv_laurentBaseChange_apply_coeffEmb
    (L : Type) [Field L] [CharZero L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (G : Type) [Group G] (δ : G →* (↥F₀ ≃ₐ[ℚ] ↥F₀)) :
    ∃ δL : G →* (↥(ModularCurve.laurentBaseChange L F₀) ≃ₐ[L] ↥(ModularCurve.laurentBaseChange L F₀)),
      ∀ (g : G) (x : ↥F₀) (hx : ModularCurve.coeffEmb L (x : LaurentSeries ℚ) ∈ ModularCurve.laurentBaseChange L F₀),
        ((δL g ⟨ModularCurve.coeffEmb L (x : LaurentSeries ℚ), hx⟩ : LaurentSeries L)) =
          ModularCurve.coeffEmb L (((δ g x : ↥F₀)) : LaurentSeries ℚ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_monoidHom_algEquiv_laurentBaseChange_apply_coeffEmb.solution
