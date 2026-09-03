import Definitions.Def_NumberTheory_DedekindSum
import Mathlib.Data.Int.ModEq
import P2M.Util
import P2M.Sol.S_rademacher_phi_level_congruence

theorem rademacher_phi_level_congruence (ℓ c' : ℕ) (hℓ : 1 ≤ ℓ) (a d : ℤ) (h1 : Int.ModEq ((ℓ * c' : ℕ) : ℤ) (a * d) 1) : ∃ z : ℤ, 12 * (((a + d : ℤ) : ℚ) * (1 - (ℓ : ℚ)) / (12 * ((ℓ * c' : ℕ) : ℚ)) + dedekindSum d c' - dedekindSum d (ℓ * c')) = ((Nat.gcd (ℓ - 1) 12 : ℕ) : ℚ) * z := by p2m_exact_reverting @_root_.P2MW.S_rademacher_phi_level_congruence.solution
