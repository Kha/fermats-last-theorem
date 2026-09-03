import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Rat
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_Submodule_mem_span_ratLocalizedAt_iff

theorem Submodule.mem_span_ratLocalizedAt_iff
    {V : Type*} [AddCommGroup V] [Module ℚ V] (M : Submodule ℤ V) (ℓ : ℕ) (hℓ : ℓ.Prime) (x : V) :
    x ∈ Submodule.span (GaloisRep.ratLocalizedAt ℓ) (M : Set V) ↔
      ∃ s : ℤ, ¬ (ℓ : ℤ) ∣ s ∧ s • x ∈ M := by p2m_exact_reverting @_root_.P2MW.S_Submodule_mem_span_ratLocalizedAt_iff.solution
