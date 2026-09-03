import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_notMem_and_forall_mul_eq_zero_of_flat_quotient_of_rTensor_injective

set_option autoImplicit false

universe u

open TensorProduct

theorem Ideal.exists_notMem_and_forall_mul_eq_zero_of_flat_quotient_of_rTensor_injective
    {R A K : Type u} [CommRing R] [CommRing A] [Algebra R A] [Field K] [Algebra R K]
    (J : Ideal A) (hJ : J.FG) [Module.Flat R (A ⧸ J)]
    (𝔭 : Ideal A) [𝔭.IsPrime] (hK : RingHom.ker (algebraMap R K) = 𝔭.comap (algebraMap R A))
    (hinj : Function.Injective ((Ideal.Quotient.mkₐ R J).toLinearMap.rTensor K)) :
    ∃ s : A, s ∉ 𝔭 ∧ ∀ j ∈ J, s * j = 0 := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_notMem_and_forall_mul_eq_zero_of_flat_quotient_of_rTensor_injective.solution
