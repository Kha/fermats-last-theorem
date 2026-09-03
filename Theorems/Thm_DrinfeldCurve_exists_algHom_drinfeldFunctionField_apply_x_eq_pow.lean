import Definitions.Def_DrinfeldCurve_FunctionField
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_exists_algHom_drinfeldFunctionField_apply_x_eq_pow

set_option autoImplicit false

namespace DrinfeldCurve

theorem exists_algHom_drinfeldFunctionField_apply_x_eq_pow (q : ℕ) [Fact q.Prime] (K : Type) [Field K]
    [CharP K q] [IsDomain (CoordRing q K)] (n : ℕ) :
    ∃ φ : drinfeldFunctionField q K →ₐ[K] drinfeldFunctionField q K,
      φ (algebraMap (CoordRing q K) (drinfeldFunctionField q K) (x q K)) =
          algebraMap (CoordRing q K) (drinfeldFunctionField q K) (x q K) ^ q ^ n ∧
        φ (algebraMap (CoordRing q K) (drinfeldFunctionField q K) (y q K)) =
          algebraMap (CoordRing q K) (drinfeldFunctionField q K) (y q K) ^ q ^ n := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_exists_algHom_drinfeldFunctionField_apply_x_eq_pow.solution
