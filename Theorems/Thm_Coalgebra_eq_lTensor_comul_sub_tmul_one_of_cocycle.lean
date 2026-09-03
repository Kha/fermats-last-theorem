import Mathlib
import P2M.Util
import P2M.Sol.S_Coalgebra_eq_lTensor_comul_sub_tmul_one_of_cocycle

set_option autoImplicit false

open scoped TensorProduct

theorem Coalgebra.eq_lTensor_comul_sub_tmul_one_of_cocycle
    {R : Type} [CommRing R] {L : Type} [CommRing L] [Bialgebra R L]
    {N : Type} [AddCommGroup N] [Module R N]
    (e : (N ⊗[R] L) ⊗[R] L)
    (he : (_root_.TensorProduct.assoc R (N ⊗[R] L) L L).symm ((Coalgebra.comul (R := R) (A := L)).lTensor (N ⊗[R] L) e) =
      ((_root_.TensorProduct.assoc R N L L).symm.toLinearMap.rTensor L)
          (((Coalgebra.comul (R := R) (A := L)).lTensor N).rTensor L e) +
        e ⊗ₜ[R] (1 : L)) :
    e = (_root_.TensorProduct.assoc R N L L).symm
          ((Coalgebra.comul (R := R) (A := L)).lTensor N
            ((_root_.TensorProduct.rid R N).toLinearMap.rTensor L
              (((Coalgebra.counit (R := R) (A := L)).lTensor N).rTensor L e))) -
        ((_root_.TensorProduct.rid R N).toLinearMap.rTensor L
              (((Coalgebra.counit (R := R) (A := L)).lTensor N).rTensor L e)) ⊗ₜ[R] (1 : L) := by p2m_exact_reverting @_root_.P2MW.S_Coalgebra_eq_lTensor_comul_sub_tmul_one_of_cocycle.solution
