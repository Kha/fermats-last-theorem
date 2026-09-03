import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_trace_eq_dual_lmul_of_bijective_rTensor

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.trace_eq_dual_lmul_of_bijective_rTensor
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A] [Module.Finite R A] [Module.Free R A]
    (τ : Module.Dual R A) (Δ : A ⊗[R] A)
    (hbal : ∀ s : A, (s ⊗ₜ[R] (1 : A)) * Δ = ((1 : A) ⊗ₜ[R] s) * Δ)
    (hbij : Function.Bijective (fun φ : Module.Dual R A => TensorProduct.lid R A (LinearMap.rTensor A φ Δ)))
    (hτ : TensorProduct.lid R A (LinearMap.rTensor A τ Δ) = 1) (x : A) :
    Algebra.trace R A x = τ (LinearMap.mul' R A Δ * x) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_trace_eq_dual_lmul_of_bijective_rTensor.solution
