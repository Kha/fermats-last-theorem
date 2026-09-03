import Mathlib
import P2M.Util
import P2M.Sol.S_DeligneSerre_exists_minimalPrime_le

theorem DeligneSerre.exists_minimalPrime_le {T : Type*} [CommRing T] [Module.Finite ℤ T] [Module.IsTorsionFree ℤ T]
  (𝔪 : Ideal T) (h𝔪 : 𝔪.IsPrime) : ∃ 𝔭 ∈ minimalPrimes T, 𝔭 ≤ 𝔪 ∧ ∀ (n : ℤ), (algebraMap ℤ T) n ∈ 𝔭 → n = 0 := by p2m_exact_reverting @_root_.P2MW.S_DeligneSerre_exists_minimalPrime_le.solution
