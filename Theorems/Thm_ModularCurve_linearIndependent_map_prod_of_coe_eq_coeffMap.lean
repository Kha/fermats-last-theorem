import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_linearIndependent_map_prod_of_coe_eq_coeffMap
set_option synthInstance.maxHeartbeats 400000

open ModularCurve
theorem ModularCurve.linearIndependent_map_prod_of_coe_eq_coeffMap
    {k₀ k : Type*} [Field k₀] [Field k] (σ : k₀ →+* k)
    (F₀ : IntermediateField k₀ (LaurentSeries k₀)) (F : IntermediateField k (LaurentSeries k))
    (ι : F₀ →+* F) (hι : ∀ x : F₀, ((ι x : F) : LaurentSeries k) = coeffMap σ (x : LaurentSeries k₀))
    {n : ℕ} {v : Fin n → F₀ × F₀} (hv : LinearIndependent k₀ v) :
    LinearIndependent k (fun j => ((ι (v j).1 : F), (ι (v j).2 : F))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_linearIndependent_map_prod_of_coe_eq_coeffMap.solution
