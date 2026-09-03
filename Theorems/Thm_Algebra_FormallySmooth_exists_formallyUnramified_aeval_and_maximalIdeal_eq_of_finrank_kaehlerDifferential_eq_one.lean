import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallySmooth_exists_formallyUnramified_aeval_and_maximalIdeal_eq_of_finrank_kaehlerDifferential_eq_one

set_option autoImplicit false

open IsLocalRing Polynomial

universe u v

theorem Algebra.FormallySmooth.exists_formallyUnramified_aeval_and_maximalIdeal_eq_of_finrank_kaehlerDifferential_eq_one
    {A : Type u} {S : Type v} [CommRing A] [IsLocalRing A] [CommRing S] [IsLocalRing S]
    [Algebra A S] [IsLocalHom (algebraMap A S)] [Algebra.FormallySmooth A S] [Algebra.EssFiniteType A S]
    (hres : Function.Surjective (algebraMap A (ResidueField S)))
    (h1 : Module.finrank S Ω[S⁄A] = 1) :
    ∃ t : S, t ∈ maximalIdeal S ∧
      (Polynomial.aeval t : A[X] →ₐ[A] S).toRingHom.FormallySmooth ∧
      (Polynomial.aeval t : A[X] →ₐ[A] S).toRingHom.FormallyUnramified ∧
      maximalIdeal S = Ideal.span {t} ⊔ (maximalIdeal A).map (algebraMap A S) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallySmooth_exists_formallyUnramified_aeval_and_maximalIdeal_eq_of_finrank_kaehlerDifferential_eq_one.solution
