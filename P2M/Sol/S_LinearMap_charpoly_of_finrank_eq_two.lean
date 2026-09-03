import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Determinant
import P2M.Util
namespace P2MW.S_LinearMap_charpoly_of_finrank_eq_two

open Polynomial

theorem solution {R : Type*} {M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (h : Module.finrank R M = 2) (f : M →ₗ[R] M) : f.charpoly = X ^ 2 - C (LinearMap.trace R M f) * X + C (LinearMap.det f) := by
  let b := Module.finBasisOfFinrankEq R M h
  rw [← f.charpoly_toMatrix b, Matrix.charpoly_fin_two, ← LinearMap.trace_eq_matrix_trace R b f,
    LinearMap.det_toMatrix b f]
