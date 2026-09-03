import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_ofIdealTop_mul
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

open TopologicalSpace Opposite
universe u

theorem solution {X : Scheme.{u}} (I J : Ideal Γ(X, ⊤)) :
    Scheme.IdealSheafData.ofIdealTop (I * J) = Scheme.IdealSheafData.ofIdealTop I * Scheme.IdealSheafData.ofIdealTop J := by
  apply Scheme.IdealSheafData.ext
  funext U
  simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_mul]
