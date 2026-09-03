import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_linearIndependent_coeffMap

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.linearIndependent_coeffMap {k₀ k : Type*} [Field k₀] [Field k] (σ : k₀ →+* k)
    {n : ℕ} {v : Fin n → LaurentSeries k₀} (hv : LinearIndependent k₀ v) :
    LinearIndependent k (fun i => coeffMap σ (v i)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_linearIndependent_coeffMap.solution
