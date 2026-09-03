import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import P2M.Util
import P2M.Sol.S_Submodule_ofFiniteIdele_diagonal_mul

open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField

theorem Submodule.ofFiniteIdele_diagonal_mul
    {D : Type*} [Ring D] [Algebra ℚ D]
    (Λ : Submodule ℤ D) (δ : Dˣ) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Submodule.ofFiniteIdele Λ (Submodule.finiteIdeleDiagonal D δ * g)
      = δ • Submodule.ofFiniteIdele Λ g := by p2m_exact_reverting @_root_.P2MW.S_Submodule_ofFiniteIdele_diagonal_mul.solution
