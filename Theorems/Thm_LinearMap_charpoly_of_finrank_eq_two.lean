import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Determinant
import P2M.Util
import P2M.Sol.S_LinearMap_charpoly_of_finrank_eq_two

open Polynomial

theorem LinearMap.charpoly_of_finrank_eq_two {R : Type*} {M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (h : Module.finrank R M = 2) (f : M →ₗ[R] M) : f.charpoly = X ^ 2 - C (LinearMap.trace R M f) * X + C (LinearMap.det f) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_charpoly_of_finrank_eq_two.solution
