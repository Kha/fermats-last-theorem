import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic
import P2M.Util
import P2M.Sol.S_TwoChartCech_GrothendieckComplex_nonempty_of_isLocalRing

universe u

open scoped TensorProduct

theorem TwoChartCech.GrothendieckComplex.nonempty_of_isLocalRing {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    Nonempty (TwoChartCech.GrothendieckComplex d) := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_GrothendieckComplex_nonempty_of_isLocalRing.solution
