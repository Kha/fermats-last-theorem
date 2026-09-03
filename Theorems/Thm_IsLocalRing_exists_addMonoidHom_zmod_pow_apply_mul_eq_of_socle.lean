import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_addMonoidHom_zmod_pow_apply_mul_eq_of_socle

set_option autoImplicit false
theorem IsLocalRing.exists_addMonoidHom_zmod_pow_apply_mul_eq_of_socle
    {B : Type} [CommRing B] [IsLocalRing B] [Finite B] (p : ℕ) [Fact p.Prime]
    (hpB : (p : B) ∈ IsLocalRing.maximalIdeal B)
    (t : B) (ht0 : t ≠ 0) (htk : ∀ m ∈ IsLocalRing.maximalIdeal B, t * m = 0) :
    ∃ N : ℕ, 1 ≤ N ∧ (p : B) ^ N = 0 ∧
      ∀ Λ : IsLocalRing.ResidueField B →+ ZMod p, ∃ π : B →+ ZMod (p ^ N),
        ∀ c : B, π (t * c) = ((Λ (IsLocalRing.residue B c)).val : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ (N - 1) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_addMonoidHom_zmod_pow_apply_mul_eq_of_socle.solution
