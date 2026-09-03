import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_ker_eq_span_range_of_forall_exists_alternating

set_option autoImplicit false

universe u v w w'

open scoped TensorProduct

theorem Algebra.injective_liftBaseChange_h1CotangentMap_of_ker_eq_span_range_of_forall_exists_alternating
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {T : Type w} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Flat S T]
    {ι : Type w'} (x : ι → T)
    (hx : Function.Surjective (MvPolynomial.aeval x : MvPolynomial ι S →ₐ[S] T))
    {n : ℕ} (f : Fin n → MvPolynomial ι S)
    (hf : RingHom.ker (MvPolynomial.aeval x : MvPolynomial ι S →ₐ[S] T) =
      Ideal.span (Set.range f))
    (hsyz : ∀ c : Fin n → MvPolynomial ι S, ∑ j, c j * f j = 0 →
      ∃ d : Fin n → Fin n → MvPolynomial ι S,
        (∀ j, d j j = 0) ∧ (∀ j l, d j l = -d l j) ∧ ∀ j, c j = ∑ l, f l * d j l) :
    Function.Injective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_ker_eq_span_range_of_forall_exists_alternating.solution
