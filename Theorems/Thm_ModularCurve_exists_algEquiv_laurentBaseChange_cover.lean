import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algEquiv_laurentBaseChange_cover

theorem ModularCurve.exists_algEquiv_laurentBaseChange_cover
    (L : Type*) [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (σ₀ : ↥F₀ ≃+* ↥F₀) :
    ∃ τ : ↥(ModularCurve.laurentBaseChange L F₀) ≃ₐ[L] ↥(ModularCurve.laurentBaseChange L F₀),
      ∀ y : ↥F₀,
        ((τ ⟨ModularCurve.coeffEmb L (y : LaurentSeries ℚ),
              ModularCurve.coeffEmb_mem_laurentBaseChange L y.2⟩ :
            ↥(ModularCurve.laurentBaseChange L F₀)) : LaurentSeries L)
          = ModularCurve.coeffEmb L ((σ₀ y : ↥F₀) : LaurentSeries ℚ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_cover.solution
