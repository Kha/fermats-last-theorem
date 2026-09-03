import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import P2M.Util
namespace P2MW.S_QuaternionAlgebra_nrd_mul
open scoped Quaternion
open QuaternionAlgebra

theorem solution {R : Type*} [CommRing R] {a b : R}
    (x y : ℍ[R, a, b]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [mk_mul_mk, nrd_mk]
  ring
