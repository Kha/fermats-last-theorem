import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_det_dual_mul_mul_eq_norm_mul_det

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.det_dual_mul_mul_eq_norm_mul_det
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (τ : Module.Dual R A) (c : A) :
    (Matrix.of fun i j => τ (c * b i * b j)).det = Algebra.norm R c * (Matrix.of fun i j => τ (b i * b j)).det := by p2m_exact_reverting @_root_.P2MW.S_Algebra_det_dual_mul_mul_eq_norm_mul_det.solution
