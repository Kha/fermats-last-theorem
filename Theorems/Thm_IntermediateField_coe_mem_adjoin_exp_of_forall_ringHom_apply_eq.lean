import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_coe_mem_adjoin_exp_of_forall_ringHom_apply_eq

set_option autoImplicit false

theorem IntermediateField.coe_mem_adjoin_exp_of_forall_ringHom_apply_eq
    (N p : ℕ) [NeZero N] (hp : p ∣ N)
    (z : ↥(IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} : Set ℂ)))
    (hz : ∀ s : ℕ, s.Coprime N → s ≡ 1 [MOD p] →
      ∀ φ : ↥(IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} : Set ℂ)) →+* ℂ,
        (∀ w : ↥(IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} : Set ℂ)),
            (w : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
            φ w = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s) →
        φ z = z) :
    (z : ℂ) ∈ IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ) := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_coe_mem_adjoin_exp_of_forall_ringHom_apply_eq.solution
