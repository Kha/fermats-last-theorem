import Mathlib
import P2M.Util
import P2M.Sol.S_AlgHom_natCard_dvd_finrank_of_forall_exists_comp_algEquiv_eq_of_isAlgClosed

set_option autoImplicit false

universe u v

theorem AlgHom.natCard_dvd_finrank_of_forall_exists_comp_algEquiv_eq_of_isAlgClosed
    (k : Type u) (B : Type v) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B] [Module.Finite k B]
    (htrans : ∀ φ ψ : B →ₐ[k] k, ∃ σ : B ≃ₐ[k] B, φ.comp (σ : B →ₐ[k] B) = ψ) :
    Nat.card (B →ₐ[k] k) ∣ Module.finrank k B := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_natCard_dvd_finrank_of_forall_exists_comp_algEquiv_eq_of_isAlgClosed.solution
