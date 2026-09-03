import Mathlib
import P2M.Util
import P2M.Sol.S_Bialgebra_fst_mul_withConv_algHom_dualNumber_eq_counit

set_option autoImplicit false

theorem Bialgebra.fst_mul_withConv_algHom_dualNumber_eq_counit
    (k : Type) [CommRing k] (B : Type) [CommRing B] [Bialgebra k B]
    (D₁ D₂ : B →ₐ[k] DualNumber k)
    (h₁ : ∀ b : B, TrivSqZeroExt.fst (D₁ b) = Bialgebra.counitAlgHom k B b)
    (h₂ : ∀ b : B, TrivSqZeroExt.fst (D₂ b) = Bialgebra.counitAlgHom k B b) (b : B) :
    TrivSqZeroExt.fst (WithConv.ofConv (WithConv.toConv D₁ * WithConv.toConv D₂) b) =
      Bialgebra.counitAlgHom k B b := by p2m_exact_reverting @_root_.P2MW.S_Bialgebra_fst_mul_withConv_algHom_dualNumber_eq_counit.solution
