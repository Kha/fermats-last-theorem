import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_integral_integral_integral_comm_of_integrable_prod_prod

set_option autoImplicit false

open MeasureTheory Set

theorem MeasureTheory.integral_integral_integral_comm_of_integrable_prod_prod
    {X Y Z E : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (ρ : Measure Z) [SFinite μ] [SFinite ν] [SFinite ρ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : X × Y × Z → E) (hf : Integrable f (μ.prod (ν.prod ρ))) :
    ∫ x, ∫ y, ∫ z, f (x, y, z) ∂ρ ∂ν ∂μ = ∫ z, ∫ y, ∫ x, f (x, y, z) ∂μ ∂ν ∂ρ := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_integral_integral_integral_comm_of_integrable_prod_prod.solution
