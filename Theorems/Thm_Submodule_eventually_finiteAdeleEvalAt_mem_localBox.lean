import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_Submodule_eventually_finiteAdeleEvalAt_mem_localBox

open scoped TensorProduct
open IsDedekindDomain NumberField

theorem Submodule.eventually_finiteAdeleEvalAt_mem_localBox
    {D : Type*} [Ring D] [Algebra ℚ D]
    (Λ : Submodule ℤ D) (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤)
    (x : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) :
    ∀ᶠ v in Filter.cofinite, Submodule.finiteAdeleEvalAt D v x ∈ Submodule.localBox Λ v := by p2m_exact_reverting @_root_.P2MW.S_Submodule_eventually_finiteAdeleEvalAt_mem_localBox.solution
