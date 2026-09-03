import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Finrank
import P2M.Util
import P2M.Sol.S_TwoChartCech_finrank_ker_baseChange_eq_of_field_extension

universe u

open scoped TensorProduct

theorem TwoChartCech.finrank_ker_baseChange_eq_of_field_extension
    {R : Type u} [CommRing R] {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1) (K L : Type u) [Field K] [Field L] [Algebra R K] [Algebra R L] [Algebra K L]
    [IsScalarTower R K L] :
    Module.finrank K (LinearMap.ker (d.baseChange K)) = Module.finrank L (LinearMap.ker (d.baseChange L)) := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_finrank_ker_baseChange_eq_of_field_extension.solution
