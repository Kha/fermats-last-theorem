import Mathlib.LinearAlgebra.TensorProduct.Tower
import P2M.Util
import P2M.Sol.S_TensorProduct_mem_span_unitTmul_of_forall_apply_eq_zero

set_option autoImplicit false
open scoped TensorProduct

theorem TensorProduct.mem_span_unitTmul_of_forall_apply_eq_zero
    {R S K T : Type}
    [CommRing R]
    [CommRing S] [Algebra R S]
    [Field K] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    [AddCommGroup T] [Module R T] [NoZeroSMulDivisors R T]
    (hinj : Function.Injective (algebraMap R K))
    {ι : Type} (Φ : ι → (K ⊗[S] (S ⊗[R] T)) →ₗ[K] (K ⊗[S] (S ⊗[R] T))) (g : ι → T → T)
    (hcomm : ∀ (i : ι) (k : K) (x : T),
      Φ i (k ⊗ₜ[S] ((1 : S) ⊗ₜ[R] x)) = k ⊗ₜ[S] ((1 : S) ⊗ₜ[R] g i x))
    (v : K ⊗[S] (S ⊗[R] T)) (hv : ∀ i, Φ i v = 0) :
    v ∈ Submodule.span K
      {z : K ⊗[S] (S ⊗[R] T) | ∃ y : T, (∀ i, g i y = 0) ∧
        z = (1 : K) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] y)} := by p2m_exact_reverting @_root_.P2MW.S_TensorProduct_mem_span_unitTmul_of_forall_apply_eq_zero.solution
