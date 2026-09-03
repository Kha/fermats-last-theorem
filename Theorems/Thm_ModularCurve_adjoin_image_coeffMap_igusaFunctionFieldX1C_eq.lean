import Mathlib
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_adjoin_image_coeffMap_igusaFunctionFieldX1C_eq

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.adjoin_image_coeffMap_igusaFunctionFieldX1C_eq
    (κ : Type*) [Field κ] (k : Type*) [Field k] [Algebra κ k] (M : ℕ)
    (w : IntegralWeightOneForm κ M) (w' : IntegralWeightOneForm k M) :
    IntermediateField.adjoin k
        (⇑(coeffMap (algebraMap κ k)) '' (igusaFunctionFieldX1C κ M w : Set (LaurentSeries κ))) =
      igusaFunctionFieldX1C k M w' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_adjoin_image_coeffMap_igusaFunctionFieldX1C_eq.solution
