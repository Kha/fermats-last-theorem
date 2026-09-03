import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_isDomain_and_isIntegrallyClosed_of_isReduced_fibre

open scoped TensorProduct

universe u

theorem Algebra.TensorProduct.isDomain_and_isIntegrallyClosed_of_isReduced_fibre
    {R B R' K' k' : Type u} [CommRing R] [CommRing B] [Algebra R B] [Module.Flat R B]
    [CommRing R'] [Algebra R R'] (ϖ : R') (hϖ : ϖ ∈ nonZeroDivisors R')
    [CommRing K'] [Algebra R' K'] [IsLocalization.Away ϖ K'] [Algebra R K'] [IsScalarTower R R' K']
    [IsDomain (K' ⊗[R] B)] [IsIntegrallyClosed (K' ⊗[R] B)]
    [CommRing k'] [Algebra R' k'] [Algebra R k'] [IsScalarTower R R' k']
    (hk : Function.Surjective (algebraMap R' k')) (hker : RingHom.ker (algebraMap R' k') = Ideal.span {ϖ})
    (hred : IsReduced (k' ⊗[R] B)) :
    IsDomain (R' ⊗[R] B) ∧ IsIntegrallyClosed (R' ⊗[R] B) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_isDomain_and_isIntegrallyClosed_of_isReduced_fibre.solution
