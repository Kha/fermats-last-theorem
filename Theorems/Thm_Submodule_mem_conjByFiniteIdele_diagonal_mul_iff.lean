import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import P2M.Util
import P2M.Sol.S_Submodule_mem_conjByFiniteIdele_diagonal_mul_iff

open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField

theorem Submodule.mem_conjByFiniteIdele_diagonal_mul_iff
    {D : Type*} [Ring D] [Algebra ℚ D] (Λ : Submodule ℤ D) (γ : Dˣ) (β : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (z : D) :
    z ∈ Submodule.conjByFiniteIdele Λ (Submodule.finiteIdeleDiagonal D γ * β) ↔
      (↑γ⁻¹ : D) * z * γ ∈ Submodule.conjByFiniteIdele Λ β := by p2m_exact_reverting @_root_.P2MW.S_Submodule_mem_conjByFiniteIdele_diagonal_mul_iff.solution
