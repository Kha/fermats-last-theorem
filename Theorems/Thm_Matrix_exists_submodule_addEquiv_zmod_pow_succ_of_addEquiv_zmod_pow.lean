import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow

set_option autoImplicit false

theorem Matrix.exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow
    (ℓ : ℕ) [Fact ℓ.Prime] (e : ℕ)
    (I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e + 1)))) (Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e + 1)))))
    (hI : Nonempty (↥I ≃+ (ZMod (ℓ ^ e) × ZMod (ℓ ^ e)))) :
    ∃ J : Submodule (Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e + 1)))) (Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e + 1)))),
      I ≤ J ∧ Nonempty (↥J ≃+ (ZMod (ℓ ^ (e + 1)) × ZMod (ℓ ^ (e + 1)))) ∧
      ∀ x ∈ J, (ℓ : Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e + 1)))) • x ∈ I := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow.solution
