import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Finrank
import P2M.Util
import P2M.Sol.S_TwoChartCech_nonempty_kerBaseChangeTowerEquiv

universe u

open scoped TensorProduct

theorem TwoChartCech.nonempty_kerBaseChangeTowerEquiv
    {R : Type u} [CommRing R] {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1) (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] :
    ∃ e : LinearMap.ker ((d.baseChange S).baseChange T) ≃ₗ[T] LinearMap.ker (d.baseChange T),
      ∀ z, (e z : T ⊗[R] C0) = TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T C0 z := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_nonempty_kerBaseChangeTowerEquiv.solution
