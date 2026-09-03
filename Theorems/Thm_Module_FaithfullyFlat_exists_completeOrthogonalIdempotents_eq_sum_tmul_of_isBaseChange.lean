import Mathlib
import P2M.Util
import P2M.Sol.S_Module_FaithfullyFlat_exists_completeOrthogonalIdempotents_eq_sum_tmul_of_isBaseChange

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem Module.FaithfullyFlat.exists_completeOrthogonalIdempotents_eq_sum_tmul_of_isBaseChange
    (A : Type u) [CommRing A] [Module.FaithfullyFlat ℤ A]
    {G : Type v} [AddCommGroup G] [Fintype G]
    (e : G → A ⊗[ℤ] A) (he : CompleteOrthogonalIdempotents e)
    (M : Submodule ℤ (G → A))
    (hM : ∀ f : G → A, f ∈ M ↔ ∀ k, ∑ m, e m * (f (k - m) ⊗ₜ[ℤ] 1) = 1 ⊗ₜ[ℤ] f k)
    (hbc : IsBaseChange A M.subtype) :
    ∃ d : G → A, CompleteOrthogonalIdempotents d ∧ ∀ k, e k = ∑ i, d i ⊗ₜ[ℤ] d (i - k) := by p2m_exact_reverting @_root_.P2MW.S_Module_FaithfullyFlat_exists_completeOrthogonalIdempotents_eq_sum_tmul_of_isBaseChange.solution
