import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.linearIndependent_coeffMap_comp_of_linearIndependent
    (κ : Type*) [Field κ] (k : Type*) [Field k] [Algebra κ k]
    {n : ℕ} (f : Fin n → LaurentSeries κ) (hf : LinearIndependent κ f) :
    LinearIndependent k (⇑(coeffMap (algebraMap κ k)) ∘ f) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent.solution
