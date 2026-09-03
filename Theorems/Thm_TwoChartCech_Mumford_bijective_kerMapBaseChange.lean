import Definitions.Def_AlgebraicGeometry_MumfordTruncation
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.RingTheory.Flat.Basic
import P2M.Util
import P2M.Sol.S_TwoChartCech_Mumford_bijective_kerMapBaseChange

universe u

open scoped TensorProduct

theorem TwoChartCech.Mumford.bijective_kerMapBaseChange
    {R : Type u} [CommRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1] [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]
    (A : Type u) [CommRing A] [Algebra R A] :
    Function.Bijective
      (TwoChartCech.kerMapBaseChange (TwoChartCech.Mumford.dK d) d (TwoChartCech.Mumford.ι0 d)
        (TwoChartCech.Mumford.ι1 d) (TwoChartCech.Mumford.comm d) A) := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_Mumford_bijective_kerMapBaseChange.solution
