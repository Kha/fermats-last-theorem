import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_Submodule_mem_localBox_iff_exists_eq_sum_basis_tmul

open scoped TensorProduct
open IsDedekindDomain NumberField

theorem Submodule.mem_localBox_iff_exists_eq_sum_basis_tmul
    {D : Type*} [Ring D] [Algebra ℚ D] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℚ D) (Λ : Submodule ℤ D) (hb : Submodule.span ℤ (Set.range b) = Λ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (x : D ⊗[ℚ] v.adicCompletion ℚ) :
    x ∈ Submodule.localBox Λ v ↔
      ∃ c : ι → v.adicCompletion ℚ,
        (∀ i, c i ∈ v.adicCompletionIntegers ℚ) ∧ x = ∑ i, b i ⊗ₜ[ℚ] c i := by p2m_exact_reverting @_root_.P2MW.S_Submodule_mem_localBox_iff_exists_eq_sum_basis_tmul.solution
