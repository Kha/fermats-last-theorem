import Mathlib
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import P2M.Util
import P2M.Sol.S_ModularCurve_intersectionAlpha_x0MqResolvedTable_inl

set_option autoImplicit false

open MazurRapoportAppendix ModularCurve

theorem ModularCurve.intersectionAlpha_x0MqResolvedTable_inl
    {node : Type} [Fintype node] [DecidableEq node] (width : node → ℕ) (hw : ∀ x, 1 ≤ width x)
    (c : X0MqComponents width → ℤ) (b : Fin 2) :
    intersectionAlpha (x0MqResolvedTable width) c (Sum.inl b) =
      (∑ x, c (DRResolvedModelPackage.chainPos width x (if b = 0 then 1 else width x - 1))) -
        (Fintype.card node : ℤ) * c (Sum.inl b) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_intersectionAlpha_x0MqResolvedTable_inl.solution
