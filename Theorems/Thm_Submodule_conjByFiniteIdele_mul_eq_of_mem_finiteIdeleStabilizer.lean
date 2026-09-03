import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import P2M.Util
import P2M.Sol.S_Submodule_conjByFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer

open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField

theorem Submodule.conjByFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer
    {D : Type*} [Ring D] [Algebra ℚ D] (Λ : Submodule ℤ D)
    (h1 : (1 : D) ∈ Λ) (hmul : ∀ x y : D, x ∈ Λ → y ∈ Λ → x * y ∈ Λ)
    (β μ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hμ : μ ∈ Submodule.finiteIdeleStabilizer Λ) :
    Submodule.conjByFiniteIdele Λ (β * μ) = Submodule.conjByFiniteIdele Λ β := by p2m_exact_reverting @_root_.P2MW.S_Submodule_conjByFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer.solution
