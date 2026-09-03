import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Data.Nat.Prime.Defs
import P2M.Util
import P2M.Sol.S_Ideal_exists_prime_natCast_mem_of_isMaximal

theorem Ideal.exists_prime_natCast_mem_of_isMaximal {T : Type*} [CommRing T] [Module.Finite ℤ T] (𝔪 : Ideal T) (h𝔪 : 𝔪.IsMaximal) : ∃ p : ℕ, p.Prime ∧ (p : T) ∈ 𝔪 := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_prime_natCast_mem_of_isMaximal.solution
