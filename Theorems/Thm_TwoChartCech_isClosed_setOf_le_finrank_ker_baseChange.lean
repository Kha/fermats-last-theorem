import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import P2M.Util
import P2M.Sol.S_TwoChartCech_isClosed_setOf_le_finrank_ker_baseChange
attribute [-simp] CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem TwoChartCech.isClosed_setOf_le_finrank_ker_baseChange
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)]
    {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) (n : ℕ) :
    IsClosed {x : T | n ≤ Module.finrank (f.base x).asIdeal.ResidueField
      (LinearMap.ker (d.baseChange (f.base x).asIdeal.ResidueField))} := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_isClosed_setOf_le_finrank_ker_baseChange.solution
