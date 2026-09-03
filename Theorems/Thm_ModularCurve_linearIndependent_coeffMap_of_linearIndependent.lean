import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_linearIndependent_coeffMap_of_linearIndependent

set_option autoImplicit false

theorem ModularCurve.linearIndependent_coeffMap_of_linearIndependent
    (κ₀ K : Type) [Field κ₀] [Field K] (φ : κ₀ →+* K)
    (ι : Type) [Fintype ι] (x : ι → LaurentSeries κ₀) (hx : LinearIndependent κ₀ x) :
    LinearIndependent K (fun i => ModularCurve.coeffMap φ (x i)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_linearIndependent_coeffMap_of_linearIndependent.solution
