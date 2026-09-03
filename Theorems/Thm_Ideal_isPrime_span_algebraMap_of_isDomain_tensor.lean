import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_isPrime_span_algebraMap_of_isDomain_tensor

set_option autoImplicit false

open scoped TensorProduct

theorem Ideal.isPrime_span_algebraMap_of_isDomain_tensor
    {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A] {κ : Type*} [Field κ] [Algebra R κ]
    (ϖ : R) (hker : RingHom.ker (algebraMap R κ) = Ideal.span {ϖ}) (hmax : (Ideal.span {ϖ} : Ideal R).IsMaximal)
    [IsDomain (κ ⊗[R] A)] : (Ideal.span {algebraMap R A ϖ} : Ideal A).IsPrime := by p2m_exact_reverting @_root_.P2MW.S_Ideal_isPrime_span_algebraMap_of_isDomain_tensor.solution
