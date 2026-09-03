import Mathlib
import P2M.Util
import P2M.Sol.S_IsSMulRegular_tensorProduct_of_flat_quotSMulTop

open scoped TensorProduct

universe u v w

theorem IsSMulRegular.tensorProduct_of_flat_quotSMulTop
    {A : Type u} [CommRing A] (t : A) {B : Type v} [AddCommGroup B] [Module A B]
    {M : Type w} [AddCommGroup M] [Module A M]
    (htA : IsSMulRegular A t) (htB : IsSMulRegular B t) (htM : IsSMulRegular M t)
    [Module.Flat (A ⧸ Ideal.span {t}) (QuotSMulTop t B)] :
    IsSMulRegular (M ⊗[A] B) t := by p2m_exact_reverting @_root_.P2MW.S_IsSMulRegular_tensorProduct_of_flat_quotSMulTop.solution
