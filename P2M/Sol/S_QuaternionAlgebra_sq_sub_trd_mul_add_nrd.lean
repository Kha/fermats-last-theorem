import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import P2M.Util
namespace P2MW.S_QuaternionAlgebra_sq_sub_trd_mul_add_nrd
open scoped Quaternion
open QuaternionAlgebra

theorem solution {R : Type*} [CommRing R] {a b : R} (x : ℍ[R, a, b]) :
    x * x - ((trd x : R) : ℍ[R, a, b]) * x + ((nrd x : R) : ℍ[R, a, b]) = 0 := by
  have h1 : ((trd x : R) : ℍ[R, a, b]) = x + star x := (add_star_eq_coe_trd x).symm
  have h2 : ((nrd x : R) : ℍ[R, a, b]) = star x * x := (star_mul_eq_coe_nrd x).symm
  rw [h1, h2, add_mul]
  abel
