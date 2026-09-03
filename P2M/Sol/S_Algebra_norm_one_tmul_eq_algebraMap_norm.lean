import Mathlib
import P2M.Util
namespace P2MW.S_Algebra_norm_one_tmul_eq_algebraMap_norm

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem solution
    {K : Type u} [CommRing K] {L : Type v} [Ring L] [Algebra K L] [Module.Free K L] [Module.Finite K L]
    (K' : Type w) [CommRing K'] [Algebra K K'] (x : L) :
    Algebra.norm K' ((1 : K') ⊗ₜ[K] x : K' ⊗[K] L) = algebraMap K K' (Algebra.norm K x) := by
  classical
  rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  apply LinearMap.ext
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul c l => simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  | add y z hy hz => simp only [map_add, hy, hz]
