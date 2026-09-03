import Definitions.Def_AlgebraicGeometry_MumfordTruncation
import Theorems.Thm_TwoChartCech_Mumford_finite_K0
import Theorems.Thm_TwoChartCech_Mumford_flat_K0
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.FinitePresentation
import P2M.Util
namespace P2MW.S_TwoChartCech_Mumford_projective_K0

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u v w

open TwoChartCech.Mumford in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    Module.Projective R (TwoChartCech.Mumford.K0 d) := by
  haveI := TwoChartCech.Mumford.finite_K0 d
  haveI := TwoChartCech.Mumford.flat_K0 d
  haveI : Module.FinitePresentation R (K0 d) := Module.finitePresentation_of_finite R _
  exact Module.Flat.projective_of_finitePresentation

end
