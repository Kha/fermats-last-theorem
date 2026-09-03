import Mathlib
import P2M.Util
import P2M.Sol.S_Bialgebra_exists_equiv_withConv_algHom_dualNumber_over_counit_baseChange_apply_one_tmul

set_option autoImplicit false

open scoped TensorProduct

theorem Bialgebra.exists_equiv_withConv_algHom_dualNumber_over_counit_baseChange_apply_one_tmul
    (R : Type) [CommRing R] (k : Type) [CommRing k] [Algebra R k]
    (H : Type) [CommRing H] [Bialgebra R H] :
    ∃ β : {D : WithConv (H →ₐ[R] DualNumber k) //
            ∀ h : H, TrivSqZeroExt.fst (D.ofConv h) = algebraMap R k (Bialgebra.counitAlgHom R H h)} ≃
          {D : k ⊗[R] H →ₐ[k] DualNumber k //
            ∀ b : k ⊗[R] H, TrivSqZeroExt.fst (D b) = Bialgebra.counitAlgHom k (k ⊗[R] H) b},
      ∀ (D : {D : WithConv (H →ₐ[R] DualNumber k) //
            ∀ h : H, TrivSqZeroExt.fst (D.ofConv h) = algebraMap R k (Bialgebra.counitAlgHom R H h)})
        (h : H), (β D).1 ((1 : k) ⊗ₜ[R] h) = D.1.ofConv h := by p2m_exact_reverting @_root_.P2MW.S_Bialgebra_exists_equiv_withConv_algHom_dualNumber_over_counit_baseChange_apply_one_tmul.solution
