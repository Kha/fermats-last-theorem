import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_exists_isCompl_forall_mem_of_compactSpace_of_continuous

set_option autoImplicit false

universe u v

open MeasureTheory

theorem Representation.exists_isCompl_forall_mem_of_compactSpace_of_continuous
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    {E : Type v} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (π : Representation ℂ H E) (hπ : ∀ (ℓ : Module.Dual ℂ E) (v : E), Continuous fun k => ℓ (π k v))
    (P : Submodule ℂ E) (hP : ∀ k : H, ∀ v ∈ P, π k v ∈ P) :
    ∃ Pc : Submodule ℂ E, IsCompl P Pc ∧ ∀ k : H, ∀ v ∈ Pc, π k v ∈ Pc := by p2m_exact_reverting @_root_.P2MW.S_Representation_exists_isCompl_forall_mem_of_compactSpace_of_continuous.solution
