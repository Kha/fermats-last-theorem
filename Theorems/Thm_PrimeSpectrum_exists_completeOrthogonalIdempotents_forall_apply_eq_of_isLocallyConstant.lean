import Mathlib
import P2M.Util
import P2M.Sol.S_PrimeSpectrum_exists_completeOrthogonalIdempotents_forall_apply_eq_of_isLocallyConstant

set_option autoImplicit false

theorem PrimeSpectrum.exists_completeOrthogonalIdempotents_forall_apply_eq_of_isLocallyConstant
    {T : Type*} [CommRing T] {Y : Type*} (f : PrimeSpectrum T → Y) (hf : IsLocallyConstant f) :
    ∃ (n : ℕ) (e : Fin n → T),
      CompleteOrthogonalIdempotents e ∧ Ideal.span (Set.range e) = ⊤ ∧
      ∀ k : Fin n, ∃ c : Y, ∀ x : PrimeSpectrum T, x ∈ PrimeSpectrum.basicOpen (e k) → f x = c := by p2m_exact_reverting @_root_.P2MW.S_PrimeSpectrum_exists_completeOrthogonalIdempotents_forall_apply_eq_of_isLocallyConstant.solution
