import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_isUnit_det_dual_mul_of_bijective

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.isUnit_det_dual_mul_of_bijective
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (τ : Module.Dual R A)
    (hτ : Function.Bijective (fun a : A => τ.comp (LinearMap.mulLeft R a))) :
    IsUnit (Matrix.of fun i j => τ (b i * b j)).det := by p2m_exact_reverting @_root_.P2MW.S_Algebra_isUnit_det_dual_mul_of_bijective.solution
