import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import P2M.Util
import P2M.Sol.S_Module_End_exists_mem_adjoin_apply_eq_self_and_apply_eq_zero_of_forall_ne_exists_ne

set_option autoImplicit false

theorem Module.End.exists_mem_adjoin_apply_eq_self_and_apply_eq_zero_of_forall_ne_exists_ne
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ι → Submodule K V) (𝒯 : Set (Module.End K V)) (c : Module.End K V → ι → K)
    (hT : ∀ T ∈ 𝒯, ∀ (i : ι), ∀ v ∈ W i, T v = c T i • v)
    (hsep : ∀ i j : ι, i ≠ j → ∃ T ∈ 𝒯, c T i ≠ c T j) (i : ι) :
    ∃ e ∈ Algebra.adjoin K 𝒯, (∀ v ∈ W i, e v = v) ∧ ∀ j : ι, j ≠ i → ∀ v ∈ W j, e v = 0 := by p2m_exact_reverting @_root_.P2MW.S_Module_End_exists_mem_adjoin_apply_eq_self_and_apply_eq_zero_of_forall_ne_exists_ne.solution
