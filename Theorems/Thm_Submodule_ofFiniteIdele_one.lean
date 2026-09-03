import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import P2M.Util
import P2M.Sol.S_Submodule_ofFiniteIdele_one

open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField

theorem Submodule.ofFiniteIdele_one {D : Type*} [Ring D] [Algebra ℚ D] (Λ : Submodule ℤ D)
    (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤) :
    Submodule.ofFiniteIdele Λ 1 = Λ := by p2m_exact_reverting @_root_.P2MW.S_Submodule_ofFiniteIdele_one.solution
