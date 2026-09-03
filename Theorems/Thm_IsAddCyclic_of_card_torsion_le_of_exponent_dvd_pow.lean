import Mathlib
import P2M.Util
import P2M.Sol.S_IsAddCyclic_of_card_torsion_le_of_exponent_dvd_pow

theorem IsAddCyclic.of_card_torsion_le_of_exponent_dvd_pow
    {G : Type*} [AddCommGroup G] [Finite G] {p : ℕ} (hp : p.Prime) (m : ℕ)
    (hexp : ∀ x : G, p ^ m • x = 0)
    (hsocle : Nat.card {x : G // p • x = 0} ≤ p) :
    IsAddCyclic G ∧ Nat.card G ∣ p ^ m := by p2m_exact_reverting @_root_.P2MW.S_IsAddCyclic_of_card_torsion_le_of_exponent_dvd_pow.solution
