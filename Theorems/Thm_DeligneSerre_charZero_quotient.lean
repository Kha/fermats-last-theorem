import Mathlib
import P2M.Util
import P2M.Sol.S_DeligneSerre_charZero_quotient

theorem DeligneSerre.charZero_quotient {T : Type*} [CommRing T] (𝔭 : Ideal T)
  (h𝔭 : ∀ (n : ℤ), (algebraMap ℤ T) n ∈ 𝔭 → n = 0) : CharZero (T ⧸ 𝔭) := by p2m_exact_reverting @_root_.P2MW.S_DeligneSerre_charZero_quotient.solution
