import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Rat
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_Submodule_mem_of_forall_prime_exists_smul_mem
import Theorems.Thm_Submodule_mem_span_ratLocalizedAt_iff
import P2M.Util
namespace P2MW.S_Submodule_eq_of_forall_prime_span_ratLocalizedAt_eq

set_option autoImplicit false

theorem solution
    {V : Type*} [AddCommGroup V] [Module ℚ V] (M N : Submodule ℤ V)
    (h : ∀ ℓ : ℕ, ℓ.Prime →
      Submodule.span (GaloisRep.ratLocalizedAt ℓ) (M : Set V) =
        Submodule.span (GaloisRep.ratLocalizedAt ℓ) (N : Set V)) : M = N := by
  apply le_antisymm
  · intro x hx
    apply Submodule.mem_of_forall_prime_exists_smul_mem
    intro ℓ hℓ
    rw [← Submodule.mem_span_ratLocalizedAt_iff N ℓ hℓ, ← h ℓ hℓ]
    exact Submodule.subset_span hx
  · intro x hx
    apply Submodule.mem_of_forall_prime_exists_smul_mem
    intro ℓ hℓ
    rw [← Submodule.mem_span_ratLocalizedAt_iff M ℓ hℓ, h ℓ hℓ]
    exact Submodule.subset_span hx
