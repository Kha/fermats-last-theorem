import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallySmooth_formallySmooth_and_formallyUnramified_aeval_of_existsUnique_smul_D_eq

set_option autoImplicit false

open Polynomial

universe u v

theorem Algebra.FormallySmooth.formallySmooth_and_formallyUnramified_aeval_of_existsUnique_smul_D_eq
    {A : Type u} {S : Type v} [CommRing A] [CommRing S] [Algebra A S] [Algebra.FormallySmooth A S]
    (t : S) (ht : ∀ ω : Ω[S⁄A], ∃! s : S, ω = s • KaehlerDifferential.D A S t) :
    (Polynomial.aeval t : A[X] →ₐ[A] S).toRingHom.FormallySmooth ∧
      (Polynomial.aeval t : A[X] →ₐ[A] S).toRingHom.FormallyUnramified := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallySmooth_formallySmooth_and_formallyUnramified_aeval_of_existsUnique_smul_D_eq.solution
