import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_relfinrank_adjoin_jqModC_pow_adjoin_jqModC_eq

set_option autoImplicit false

theorem ModularCurve.relfinrank_adjoin_jqModC_pow_adjoin_jqModC_eq
    (κ : Type) [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p] :
    IntermediateField.relfinrank
        (IntermediateField.adjoin κ ({ModularCurve.jqModC κ ^ p} : Set (LaurentSeries κ)))
        (IntermediateField.adjoin κ ({ModularCurve.jqModC κ} : Set (LaurentSeries κ))) = p := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_relfinrank_adjoin_jqModC_pow_adjoin_jqModC_eq.solution
