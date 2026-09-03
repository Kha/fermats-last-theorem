import Mathlib
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import P2M.Util
import P2M.Sol.S_ModularCurve_intersectionAlpha_x0MqResolvedTable_eq_sum_x0MqAdj_and_sum_x0MqAdj_inl

set_option autoImplicit false

open MazurRapoportAppendix ModularCurve

theorem ModularCurve.intersectionAlpha_x0MqResolvedTable_eq_sum_x0MqAdj_and_sum_x0MqAdj_inl
    {node : Type} [Fintype node] [DecidableEq node] (width : node → ℕ) (hw : ∀ x, 1 ≤ width x) :
    (∀ (c : X0MqComponents width → ℤ) (j : X0MqComponents width),
      intersectionAlpha (x0MqResolvedTable width) c j =
        (∑ F, c F * (x0MqAdj width F j : ℤ)) - c j * ∑ F, (x0MqAdj width j F : ℤ)) ∧
    (∀ b : Fin 2, ∑ F, x0MqAdj width (Sum.inl b) F = Fintype.card node) ∧
    (∀ (b : Fin 2) (F : X0MqComponents width),
      x0MqAdj width F (Sum.inl b) =
        ∑ x, if F = DRResolvedModelPackage.chainPos width x (if b = 0 then 1 else width x - 1) then 1 else 0) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_intersectionAlpha_x0MqResolvedTable_eq_sum_x0MqAdj_and_sum_x0MqAdj_inl.solution
