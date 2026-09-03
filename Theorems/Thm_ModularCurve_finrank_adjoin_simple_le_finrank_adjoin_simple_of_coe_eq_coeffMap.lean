import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_finrank_adjoin_simple_le_finrank_adjoin_simple_of_coe_eq_coeffMap

set_option autoImplicit false

open ModularCurve
open scoped IntermediateField

theorem ModularCurve.finrank_adjoin_simple_le_finrank_adjoin_simple_of_coe_eq_coeffMap
    {k₀ k : Type*} [Field k₀] [Field k] (σ : k₀ →+* k)
    (F₀ : IntermediateField k₀ (LaurentSeries k₀)) (F : IntermediateField k (LaurentSeries k))
    (ι : ↥F₀ →+* ↥F) (hι : ∀ x : ↥F₀, ((ι x : ↥F) : LaurentSeries k) = coeffMap σ (x : LaurentSeries k₀))
    (t₀ : ↥F₀) (ht₀ : Transcendental k₀ t₀) [FiniteDimensional ↥k⟮ι t₀⟯ ↥F] :
    Module.finrank ↥k₀⟮t₀⟯ ↥F₀ ≤ Module.finrank ↥k⟮ι t₀⟯ ↥F := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finrank_adjoin_simple_le_finrank_adjoin_simple_of_coe_eq_coeffMap.solution
