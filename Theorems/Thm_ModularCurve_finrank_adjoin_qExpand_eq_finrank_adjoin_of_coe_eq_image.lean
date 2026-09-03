import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import P2M.Util
import P2M.Sol.S_ModularCurve_finrank_adjoin_qExpand_eq_finrank_adjoin_of_coe_eq_image

set_option autoImplicit false

open ModularCurve

universe u

theorem ModularCurve.finrank_adjoin_qExpand_eq_finrank_adjoin_of_coe_eq_image
    (κ : Type u) [Field κ] (n : ℕ) [NeZero n]
    (F F' : IntermediateField κ (LaurentSeries κ))
    (hF' : (F' : Set (LaurentSeries κ)) = ModularCurve.qExpand κ n '' (F : Set (LaurentSeries κ)))
    (x : LaurentSeries κ) :
    Module.finrank ↥F' ↥(IntermediateField.adjoin ↥F' ({ModularCurve.qExpand κ n x} : Set (LaurentSeries κ))) =
      Module.finrank ↥F ↥(IntermediateField.adjoin ↥F ({x} : Set (LaurentSeries κ))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finrank_adjoin_qExpand_eq_finrank_adjoin_of_coe_eq_image.solution
