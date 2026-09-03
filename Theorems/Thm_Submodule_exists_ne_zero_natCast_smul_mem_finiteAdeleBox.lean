import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import P2M.Util
import P2M.Sol.S_Submodule_exists_ne_zero_natCast_smul_mem_finiteAdeleBox

open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField

theorem Submodule.exists_ne_zero_natCast_smul_mem_finiteAdeleBox {D : Type*} [Ring D] [Algebra ℚ D]
    (Λ : Submodule ℤ D) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤)
    (w : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) :
    ∃ N : ℕ, N ≠ 0 ∧ (N : ℚ) • w ∈ Submodule.finiteAdeleBox Λ := by p2m_exact_reverting @_root_.P2MW.S_Submodule_exists_ne_zero_natCast_smul_mem_finiteAdeleBox.solution
