import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_isPrincipal_of_surjective_of_isDiscreteValuationRing_of_ker_eq_span_singleton_of_forall_mul_mem

set_option autoImplicit false

theorem Ideal.isPrincipal_of_surjective_of_isDiscreteValuationRing_of_ker_eq_span_singleton_of_forall_mul_mem
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (f : R →+* S) (hf : Function.Surjective f) (t : R) (hker : RingHom.ker f = Ideal.span {t})
    (P : Ideal R) (hP : ∀ r : R, t * r ∈ P → r ∈ P) :
    Submodule.IsPrincipal P := by p2m_exact_reverting @_root_.P2MW.S_Ideal_isPrincipal_of_surjective_of_isDiscreteValuationRing_of_ker_eq_span_singleton_of_forall_mul_mem.solution
