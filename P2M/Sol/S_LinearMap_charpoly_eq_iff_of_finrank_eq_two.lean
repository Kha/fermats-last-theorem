import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Determinant
import Theorems.Thm_LinearMap_charpoly_of_finrank_eq_two
import P2M.Util
namespace P2MW.S_LinearMap_charpoly_eq_iff_of_finrank_eq_two

open Polynomial

theorem solution {R : Type*} {M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (h : Module.finrank R M = 2) (f : M →ₗ[R] M) (a b : R) : f.charpoly = X ^ 2 - C a * X + C b ↔ LinearMap.trace R M f = a ∧ LinearMap.det f = b := by
  rw [LinearMap.charpoly_of_finrank_eq_two h f]
  constructor
  · intro he
    have h0 := congr_arg (fun q : R[X] ↦ q.coeff 0) he
    have h1 := congr_arg (fun q : R[X] ↦ q.coeff 1) he
    simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C] at h0 h1
    norm_num at h0 h1
    exact ⟨h1, h0⟩
  · rintro ⟨ht, hd⟩
    rw [ht, hd]
