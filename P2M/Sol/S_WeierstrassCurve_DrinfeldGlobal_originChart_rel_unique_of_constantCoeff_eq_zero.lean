import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import P2M.Util
namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_originChart_rel_unique_of_constantCoeff_eq_zero

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {σ : Type u} {R : Type u} [CommRing R] (a₁ a₂ a₃ a₄ a₆ x v v' : MvPowerSeries σ R)
    (hx : MvPowerSeries.constantCoeff x = 0) (hv : MvPowerSeries.constantCoeff v = 0)
    (hv' : MvPowerSeries.constantCoeff v' = 0)
    (h : v + a₁ * x * v + a₃ * v ^ 2 = x ^ 3 + a₂ * x ^ 2 * v + a₄ * x * v ^ 2 + a₆ * v ^ 3)
    (h' : v' + a₁ * x * v' + a₃ * v' ^ 2 = x ^ 3 + a₂ * x ^ 2 * v' + a₄ * x * v' ^ 2 + a₆ * v' ^ 3) :
    v = v' := by
  have key : (v - v') * (1 + a₁ * x + a₃ * (v + v') - a₂ * x ^ 2 - a₄ * x * (v + v') - a₆ * (v ^ 2 + v * v' + v' ^ 2)) = 0 := by
    linear_combination h - h'
  have hunit : IsUnit (1 + a₁ * x + a₃ * (v + v') - a₂ * x ^ 2 - a₄ * x * (v + v') - a₆ * (v ^ 2 + v * v' + v' ^ 2)) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    simp [hx, hv, hv']
  have := hunit.mul_left_eq_zero.mp key
  exact sub_eq_zero.mp this
