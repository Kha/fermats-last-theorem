import Mathlib
import P2M.Util
import P2M.Sol.S_Bialgebra_exists_id_eq_convMul_of_retract

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem Bialgebra.exists_id_eq_convMul_of_retract
    {k : Type u} [CommRing k] {D : Type v} [CommRing D] [Bialgebra k D] [Coalgebra.IsCocomm k D]
    {X : Type v} [CommRing X] [Bialgebra k X] [Coalgebra.IsCocomm k X]
    (r : D →ₐc[k] X) (j : X →ₐc[k] D) (hrj : r.comp j = BialgHom.id k X)
    (e : D →ₗ[k] D) (hrej : (r : D →ₗ[k] X) ∘ₗ e ∘ₗ (j : X →ₗ[k] D) = LinearMap.id)
    (FD : D →ₐ[k] D) (FX : X →ₐ[k] X) (hF : (r : D →ₐ[k] X).comp FD = FX.comp (r : D →ₐ[k] X))
    (VD : D →ₗc[k] D) (VX : X →ₗc[k] X) (hV : (VD : D →ₗ[k] D) ∘ₗ (j : X →ₗ[k] D) = (j : X →ₗ[k] D) ∘ₗ (VX : X →ₗ[k] X))
    (a b : D →ₐc[k] D)
    (he : e = (WithConv.toConv (FD.toLinearMap ∘ₗ (a : D →ₗ[k] D)) *
        WithConv.toConv ((b : D →ₗ[k] D) ∘ₗ (VD : D →ₗ[k] D))).ofConv) :
    ∃ a' b' : X →ₐc[k] X,
      a' = (r.comp a).comp j ∧ b' = (r.comp b).comp j ∧
      (LinearMap.id : X →ₗ[k] X) =
        (WithConv.toConv (FX.toLinearMap ∘ₗ (a' : X →ₗ[k] X)) *
          WithConv.toConv ((b' : X →ₗ[k] X) ∘ₗ (VX : X →ₗ[k] X))).ofConv := by p2m_exact_reverting @_root_.P2MW.S_Bialgebra_exists_id_eq_convMul_of_retract.solution
