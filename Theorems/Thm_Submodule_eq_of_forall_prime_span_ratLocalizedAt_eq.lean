import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Rat
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_Submodule_eq_of_forall_prime_span_ratLocalizedAt_eq

theorem Submodule.eq_of_forall_prime_span_ratLocalizedAt_eq
    {V : Type*} [AddCommGroup V] [Module ℚ V] (M N : Submodule ℤ V)
    (h : ∀ ℓ : ℕ, ℓ.Prime →
      Submodule.span (GaloisRep.ratLocalizedAt ℓ) (M : Set V) =
        Submodule.span (GaloisRep.ratLocalizedAt ℓ) (N : Set V)) : M = N := by p2m_exact_reverting @_root_.P2MW.S_Submodule_eq_of_forall_prime_span_ratLocalizedAt_eq.solution
