import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_isDomain_and_isIntegrallyClosed_tensor_of_isReduced_fibre

open scoped TensorProduct

universe u

theorem Subalgebra.isDomain_and_isIntegrallyClosed_tensor_of_isReduced_fibre
    {R F R' K' k' : Type u} [CommRing R] [Field F] [Algebra R F] (A : Subalgebra R F)
    [Module.Flat R A]
    [CommRing R'] [Algebra R R'] (ϖ : R') (hϖ : ϖ ∈ nonZeroDivisors R')
    [CommRing K'] [Algebra R' K'] [IsLocalization.Away ϖ K'] [Algebra R K'] [IsScalarTower R R' K']
    [IsDomain (K' ⊗[R] A)] [IsIntegrallyClosed (K' ⊗[R] A)]
    [CommRing k'] [Algebra R' k'] [Algebra R k'] [IsScalarTower R R' k']
    (hk : Function.Surjective (algebraMap R' k')) (hker : RingHom.ker (algebraMap R' k') = Ideal.span {ϖ})
    (hred : IsReduced (k' ⊗[R] A)) :
    IsDomain (R' ⊗[R] A) ∧ IsIntegrallyClosed (R' ⊗[R] A) := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_isDomain_and_isIntegrallyClosed_tensor_of_isReduced_fibre.solution
