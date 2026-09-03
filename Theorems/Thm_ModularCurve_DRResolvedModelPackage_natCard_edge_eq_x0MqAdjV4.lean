import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import P2M.Util
import P2M.Sol.S_ModularCurve_DRResolvedModelPackage_natCard_edge_eq_x0MqAdjV4

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.DRResolvedModelPackage.natCard_edge_eq_x0MqAdjV4
    {node : Type} [Fintype node] [DecidableEq node] (width : node → ℕ)
    (v w : X0MqComponents width) (hvw : v ≠ w) :
    Nat.card {e : Σ n : node, Fin (width n) //
        (v = DRResolvedModelPackage.chainPos width e.1 e.2 ∧ w = DRResolvedModelPackage.chainPos width e.1 (e.2 + 1)) ∨
          (w = DRResolvedModelPackage.chainPos width e.1 e.2 ∧ v = DRResolvedModelPackage.chainPos width e.1 (e.2 + 1))} =
      x0MqAdj width v w := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRResolvedModelPackage_natCard_edge_eq_x0MqAdjV4.solution
