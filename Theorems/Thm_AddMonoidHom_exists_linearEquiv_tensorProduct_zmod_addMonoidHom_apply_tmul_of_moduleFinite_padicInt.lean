import Mathlib
import P2M.Util
import P2M.Sol.S_AddMonoidHom_exists_linearEquiv_tensorProduct_zmod_addMonoidHom_apply_tmul_of_moduleFinite_padicInt

set_option autoImplicit false

open scoped TensorProduct

theorem AddMonoidHom.exists_linearEquiv_tensorProduct_zmod_addMonoidHom_apply_tmul_of_moduleFinite_padicInt
    (p : ℕ) [Fact p.Prime] (P : Type*) [AddCommGroup P] [Module ℤ_[p] P] [Module.Finite ℤ_[p] P]
    (B : Type*) [CommRing B] [Algebra (ZMod p) B] :
    ∃ e : B ⊗[ZMod p] (P →+ ZMod p) ≃ₗ[B] (P →+ B),
      ∀ (b : B) (φ : P →+ ZMod p) (x : P), e (b ⊗ₜ[ZMod p] φ) x = b * algebraMap (ZMod p) B (φ x) := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidHom_exists_linearEquiv_tensorProduct_zmod_addMonoidHom_apply_tmul_of_moduleFinite_padicInt.solution
