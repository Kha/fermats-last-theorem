import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_ker_eq_span_of_surjective_truncated_of_ker_eq_span

set_option autoImplicit false

theorem Algebra.exists_ker_eq_span_of_surjective_truncated_of_ker_eq_span
    (k : Type*) [Field k] (C : Type*) [CommRing C] [Algebra k C] [IsLocalRing C] [Module.Finite k C]
    (M : ℕ)
    (r : ℕ) (β : (MvPolynomial (Fin r) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin r) k →+* k)) ^ (M + 1)) →ₐ[k] C)
    (hβ : Function.Surjective β)
    (gβ : Fin r → (MvPolynomial (Fin r) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin r) k →+* k)) ^ (M + 1)))
    (hgβ : RingHom.ker β = Ideal.span (Set.range gβ))
    (N : ℕ) (α : (MvPolynomial (Fin N) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1)) →ₐ[k] C)
    (hα : Function.Surjective α) :
    ∃ h : Fin N → (MvPolynomial (Fin N) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1)),
      RingHom.ker α = Ideal.span (Set.range h) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_ker_eq_span_of_surjective_truncated_of_ker_eq_span.solution
