import Mathlib
import P2M.Util
import P2M.Sol.S_KaehlerDifferential_exists_linearMap_pi_surjective_ker_eq_span_pderiv_of_surjective

set_option autoImplicit false

open scoped TensorProduct

theorem KaehlerDifferential.exists_linearMap_pi_surjective_ker_eq_span_pderiv_of_surjective
    (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S] {m r : ℕ}
    (f : Fin r → MvPolynomial (Fin m) R) (φ : MvPolynomial (Fin m) R →ₐ[R] S) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = Ideal.span (Set.range f)) :
    ∃ Φ : (Fin m → S) →ₗ[S] Ω[S⁄R],
      Function.Surjective Φ ∧
      (∀ j : Fin m, Φ (Pi.single j 1) = KaehlerDifferential.D R S (φ (MvPolynomial.X j))) ∧
      LinearMap.ker Φ = Submodule.span S (Set.range fun i : Fin r => fun j : Fin m => φ (MvPolynomial.pderiv j (f i))) := by p2m_exact_reverting @_root_.P2MW.S_KaehlerDifferential_exists_linearMap_pi_surjective_ker_eq_span_pderiv_of_surjective.solution
