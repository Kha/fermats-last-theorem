import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete

theorem Polynomial.exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete
    {R S : Type*} [CommRing R] [CommRing S] (π : R →+* S) (hπ : Function.Surjective π)
    [IsAdicComplete (RingHom.ker π) R]
    {F : Polynomial R} (hF : F.Monic) {g₀ h₀ : Polynomial S} (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hF₀ : F.map π = g₀ * h₀) :
    ∃ g h : Polynomial R, g.Monic ∧ h.Monic ∧ g * h = F ∧
      g.map π = g₀ ∧ h.map π = h₀ ∧ IsCoprime g h ∧
      ∀ g' : Polynomial R, g'.Monic → g'.map π = g₀ → g' ∣ F → g' = g := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete.solution
