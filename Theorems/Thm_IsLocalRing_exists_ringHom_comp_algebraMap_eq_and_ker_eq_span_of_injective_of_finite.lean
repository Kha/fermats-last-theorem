import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_ringHom_comp_algebraMap_eq_and_ker_eq_span_of_injective_of_finite

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.exists_ringHom_comp_algebraMap_eq_and_ker_eq_span_of_injective_of_finite
    {A S : Type*} [CommRing A] [IsLocalRing A] [CommRing S] [Algebra A S] (t : S)
    [Module.Finite A (S ⧸ Ideal.span ({t} : Set S))]
    (hinj : Function.Injective (algebraMap A (S ⧸ Ideal.span ({t} : Set S))))
    (hfib : ∀ s : S, ∃ a : A,
      s - algebraMap A S a ∈ Ideal.span ({t} : Set S) ⊔ (maximalIdeal A).map (algebraMap A S)) :
    ∃ χ : S →+* A, (∀ a : A, χ (algebraMap A S a) = a) ∧ RingHom.ker χ = Ideal.span ({t} : Set S) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_ringHom_comp_algebraMap_eq_and_ker_eq_span_of_injective_of_finite.solution
