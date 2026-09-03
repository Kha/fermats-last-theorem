import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_existsUnique_apply_eq_of_completeOrthogonalIdempotents_of_corner_denominators

theorem RingHom.existsUnique_apply_eq_of_completeOrthogonalIdempotents_of_corner_denominators
    (K : Type) [CommRing K] (ι : Type) [Fintype ι] [DecidableEq ι]
    (e : ι → K) (he : CompleteOrthogonalIdempotents e)
    (χ : ι → (K →+* ℚ)) (hχe : ∀ a b : ι, χ b (e a) = if b = a then 1 else 0)
    (hsep : ∀ k k' : K, (∀ a, χ a k = χ a k') → k = k')
    (d : ι → ℕ) (hd : ∀ a, 0 < d a)
    (hval : ∀ (a : ι) (k : K), ∃ (n : ℕ) (m : ℤ), χ a k = m / (d a : ℚ) ^ n)
    (hinv : ∀ a : ι, ∃ y : K, χ a y = (d a : ℚ)⁻¹)
    (T : Type) [CommRing T] (b : ι → T) (hb : CompleteOrthogonalIdempotents b)
    (hbd : ∀ a : ι, ∃ v : T, v * ((d a : T) * b a) = b a) :
    ∃! φ : K →+* T, ∀ a, φ (e a) = b a := by p2m_exact_reverting @_root_.P2MW.S_RingHom_existsUnique_apply_eq_of_completeOrthogonalIdempotents_of_corner_denominators.solution
