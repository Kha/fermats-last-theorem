import Mathlib
import Definitions.Def_AlgebraicGeometry_MumfordTruncation
import Theorems.Thm_TwoChartCech_Mumford_bijective_kerMapBaseChange
import Theorems.Thm_TwoChartCech_Mumford_finite_K0
import P2M.Util
namespace P2MW.S_TwoChartCech_finite_ker_baseChange_of_finite_ker_of_finite_coker

set_option autoImplicit false

universe u

open scoped TensorProduct

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)]
    (A : Type u) [CommRing A] [Algebra R A] [IsNoetherianRing A] :
    Module.Finite A (LinearMap.ker (d.baseChange A)) := by
  have hbij := TwoChartCech.Mumford.bijective_kerMapBaseChange d A
  haveI : Module.Finite R ↥(TwoChartCech.Mumford.K0 d) := TwoChartCech.Mumford.finite_K0 d
  haveI : Module.Finite A (A ⊗[R] ↥(TwoChartCech.Mumford.K0 d)) := inferInstance
  haveI : IsNoetherian A (A ⊗[R] ↥(TwoChartCech.Mumford.K0 d)) :=
    isNoetherian_of_isNoetherianRing_of_finite A _
  haveI : Module.Finite A ↥(LinearMap.ker ((TwoChartCech.Mumford.dK d).baseChange A)) := inferInstance
  exact Module.Finite.of_surjective _ hbij.2
