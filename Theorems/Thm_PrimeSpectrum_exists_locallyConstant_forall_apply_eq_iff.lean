import Mathlib
import P2M.Util
import P2M.Sol.S_PrimeSpectrum_exists_locallyConstant_forall_apply_eq_iff

set_option autoImplicit false

open PrimeSpectrum

theorem PrimeSpectrum.exists_locallyConstant_forall_apply_eq_iff
    {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (e : ι → R) (he : CompleteOrthogonalIdempotents e) :
    ∃ f : LocallyConstant (PrimeSpectrum R) ι,
      ∀ (i : ι) (x : PrimeSpectrum R), f x = i ↔ e i ∉ x.asIdeal := by p2m_exact_reverting @_root_.P2MW.S_PrimeSpectrum_exists_locallyConstant_forall_apply_eq_iff.solution
