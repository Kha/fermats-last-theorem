import Mathlib
import P2M.Util
import P2M.Sol.S_TensorProduct_exists_linearEquiv_compHom_ringEquiv_tmul

set_option autoImplicit false

open scoped TensorProduct

theorem TensorProduct.exists_linearEquiv_compHom_ringEquiv_tmul
    {k κ : Type} [Field k] [Field κ] (e : k ≃+* κ)
    (V : Type) [AddCommGroup V] [Module k V] (H : Type) [AddCommGroup H] [Module κ H] :
    letI : Module κ V := Module.compHom V (e.symm : κ ≃+* k).toRingHom
    letI : Module k H := Module.compHom H e.toRingHom
    letI : Module k (V ⊗[κ] H) := Module.compHom (V ⊗[κ] H) e.toRingHom
    (Module.Finite k H ↔ Module.Finite κ H) ∧
    Module.finrank k H = Module.finrank κ H ∧
    ∃ Θ : (V ⊗[k] H) ≃ₗ[k] (V ⊗[κ] H),
      (∀ (v : V) (h : H), Θ (v ⊗ₜ[k] h) = v ⊗ₜ[κ] h) ∧
      (∀ (f : V →ₗ[k] V) (f' : V →ₗ[κ] V) (_ : ∀ v, f' v = f v) (g : H →ₗ[κ] H) (g' : H →ₗ[k] H) (_ : ∀ h, g' h = g h)
          (x : V ⊗[k] H),
        Θ (TensorProduct.map f g' x) = TensorProduct.map f' g (Θ x)) := by p2m_exact_reverting @_root_.P2MW.S_TensorProduct_exists_linearEquiv_compHom_ringEquiv_tmul.solution
