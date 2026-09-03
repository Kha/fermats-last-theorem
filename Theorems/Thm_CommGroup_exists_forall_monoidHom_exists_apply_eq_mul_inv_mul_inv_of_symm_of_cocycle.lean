import Mathlib
import P2M.Util
import P2M.Sol.S_CommGroup_exists_forall_monoidHom_exists_apply_eq_mul_inv_mul_inv_of_symm_of_cocycle

set_option autoImplicit false

universe u v

theorem CommGroup.exists_forall_monoidHom_exists_apply_eq_mul_inv_mul_inv_of_symm_of_cocycle
    {K : Type u} [AddCommGroup K] [Finite K] {A : Type v} [CommGroup A] (c : K → K → A)
    (hsymm : ∀ k k', c k k' = c k' k) (hcoc : ∀ k k' k'', c k k' * c (k + k') k'' = c k' k'' * c k (k' + k'')) :
    ∃ (m : ℕ) (a : Fin m → A) (n : Fin m → ℕ), (∀ i, 0 < n i ∧ n i ∣ Nat.card K) ∧
      ∀ (A' : Type v) [CommGroup A'] (φ : A →* A'), (∀ i, ∃ α : A', α ^ (n i) = φ (a i)) →
        ∃ b : K → A', ∀ k k', φ (c k k') = b (k + k') * (b k)⁻¹ * (b k')⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_CommGroup_exists_forall_monoidHom_exists_apply_eq_mul_inv_mul_inv_of_symm_of_cocycle.solution
