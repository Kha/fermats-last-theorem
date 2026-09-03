import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_finite_and_faithfullyFlat_of_maximalIdeal_eq_span_natCast_of_mem_jacobson

universe u v w

theorem RingHom.finite_and_faithfullyFlat_of_maximalIdeal_eq_span_natCast_of_mem_jacobson
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) (hpJ : (p : 𝓞) ∈ (⊥ : Ideal 𝓞).jacobson)
    (E : Type v) [CommRing E] [Algebra 𝓞 E] [Module.Free 𝓞 E] [Module.Finite 𝓞 E] [IsLocalRing E]
    (hE : IsLocalRing.maximalIdeal E = Ideal.span {(p : E)})
    (T : Type w) [CommRing T] [Algebra 𝓞 T] [Module.Free 𝓞 T] [Module.Finite 𝓞 T] [Nontrivial T]
    (ι : E →ₐ[𝓞] T) :
    ι.toRingHom.Finite ∧ ι.toRingHom.FaithfullyFlat := by p2m_exact_reverting @_root_.P2MW.S_RingHom_finite_and_faithfullyFlat_of_maximalIdeal_eq_span_natCast_of_mem_jacobson.solution
