import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct

set_option autoImplicit false

universe u

theorem Algebra.eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Type u} [CommRing B] [Algebra R B] [NoZeroSMulDivisors R B]
    [IsReduced (TensorProduct R K B)] [Module.Finite K (TensorProduct R K B)]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]
    (b : B) (hb : ∀ φ : B →ₐ[R] Ω, φ b = 0) : b = 0 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct.solution
