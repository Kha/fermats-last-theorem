import Definitions.Def_ModularCurve_ComponentGroup
import P2M.Util
import P2M.Sol.S_ModularCurve_finite_componentGroup_of_pos
attribute [-simp] ModularCurve.coordOf_apply ModularCurve.coordOfEquiv_apply ModularCurve.diffChar_coe_apply ModularCurve.gramRangeBasisOf_coe ModularCurve.gramMatrixOf_apply

theorem ModularCurve.finite_componentGroup_of_pos {ι : Type*} [Fintype ι] (e : ι → ℕ)
    (he : ∀ x, 0 < e x) : Finite (componentGroup e) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finite_componentGroup_of_pos.solution
