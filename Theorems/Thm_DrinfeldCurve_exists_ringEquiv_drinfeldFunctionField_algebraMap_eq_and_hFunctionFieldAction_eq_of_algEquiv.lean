import Definitions.Def_DrinfeldCurve_FunctionField
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_exists_ringEquiv_drinfeldFunctionField_algebraMap_eq_and_hFunctionFieldAction_eq_of_algEquiv

set_option autoImplicit false

open DrinfeldCurve

theorem DrinfeldCurve.exists_ringEquiv_drinfeldFunctionField_algebraMap_eq_and_hFunctionFieldAction_eq_of_algEquiv
    (q : ℕ) [Fact q.Prime]
    (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (DrinfeldCurve.CoordRing q k)]
    (k' : Type) [Field k'] [Algebra (GaloisField q 2) k'] [IsDomain (DrinfeldCurve.CoordRing q k')]
    (e : k ≃ₐ[GaloisField q 2] k') :
    ∃ φ : drinfeldFunctionField q k ≃+* drinfeldFunctionField q k',
      (∀ a : k, φ (algebraMap k (drinfeldFunctionField q k) a) = algebraMap k' (drinfeldFunctionField q k') (e a)) ∧
      φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (DrinfeldCurve.x q k)) =
        algebraMap (CoordRing q k') (drinfeldFunctionField q k') (DrinfeldCurve.x q k') ∧
      φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (DrinfeldCurve.y q k)) =
        algebraMap (CoordRing q k') (drinfeldFunctionField q k') (DrinfeldCurve.y q k') ∧
      (∀ (h : hSubgroup q) (f : drinfeldFunctionField q k),
        φ (hFunctionFieldAction q k h f) = hFunctionFieldAction q k' h (φ f)) := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_exists_ringEquiv_drinfeldFunctionField_algebraMap_eq_and_hFunctionFieldAction_eq_of_algEquiv.solution
