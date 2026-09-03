import Mathlib
import P2M.Util
import P2M.Sol.S_Bialgebra_eq_algebraMap_counit_of_id_eq_convMul_of_pow_eq

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem Bialgebra.eq_algebraMap_counit_of_id_eq_convMul_of_pow_eq
    {k : Type u} [CommRing k] {X : Type v} [CommRing X] [Bialgebra k X]
    (F : X →ₐ[k] X) (V : X →ₗc[k] X) (a b : X →ₐc[k] X) (m : ℕ)
    (hFa : F.comp (a : X →ₐ[k] X) = (a : X →ₐ[k] X).comp F)
    (hFb : F.comp (b : X →ₐ[k] X) = (b : X →ₐ[k] X).comp F)
    (hFm : ∀ x, (F.toLinearMap ^ m) x = algebraMap k X (Coalgebra.counit (R := k) x))
    (hVm : ∀ x, ((V : X →ₗ[k] X) ^ m) x = algebraMap k X (Coalgebra.counit (R := k) x))
    (hid : (LinearMap.id : X →ₗ[k] X) =
      (WithConv.toConv (F.toLinearMap ∘ₗ (a : X →ₗ[k] X)) *
        WithConv.toConv ((b : X →ₗ[k] X) ∘ₗ (V : X →ₗ[k] X))).ofConv) :
    ∀ x : X, x = algebraMap k X (Coalgebra.counit (R := k) x) := by p2m_exact_reverting @_root_.P2MW.S_Bialgebra_eq_algebraMap_counit_of_id_eq_convMul_of_pow_eq.solution
