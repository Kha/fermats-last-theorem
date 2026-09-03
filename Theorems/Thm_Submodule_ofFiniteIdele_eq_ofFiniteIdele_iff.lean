import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import P2M.Util
import P2M.Sol.S_Submodule_ofFiniteIdele_eq_ofFiniteIdele_iff

open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField

theorem Submodule.ofFiniteIdele_eq_ofFiniteIdele_iff
    {D : Type*} [Ring D] [Algebra ℚ D]
    (Λ : Submodule ℤ D) (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤)
    (g g' : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Submodule.ofFiniteIdele Λ g = Submodule.ofFiniteIdele Λ g' ↔
      g⁻¹ * g' ∈ Submodule.finiteIdeleStabilizer Λ := by p2m_exact_reverting @_root_.P2MW.S_Submodule_ofFiniteIdele_eq_ofFiniteIdele_iff.solution
