import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import P2M.Util
import P2M.Sol.S_Submodule_finiteAdeleBox_conjByFiniteIdele

open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField

theorem Submodule.finiteAdeleBox_conjByFiniteIdele
    {D : Type*} [Ring D] [Algebra ℚ D] (Λ : Submodule ℤ D) (hfg : Λ.FG)
    (hspan : Submodule.span ℚ (Λ : Set D) = ⊤) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Submodule.finiteAdeleBox (Submodule.conjByFiniteIdele Λ g)
      = (Submodule.finiteAdeleBox Λ).map
          ((AddMonoidHom.mulRight ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)).comp
            (AddMonoidHom.mulLeft (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))) := by p2m_exact_reverting @_root_.P2MW.S_Submodule_finiteAdeleBox_conjByFiniteIdele.solution
