import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import P2M.Util
import P2M.Sol.S_Submodule_fg_and_span_eq_top_ofFiniteIdele

open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField

theorem Submodule.fg_and_span_eq_top_ofFiniteIdele {D : Type*} [Ring D] [Algebra ℚ D]
    (Λ : Submodule ℤ D) (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤)
    (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    (Submodule.ofFiniteIdele Λ g).FG ∧
      Submodule.span ℚ ((Submodule.ofFiniteIdele Λ g : Submodule ℤ D) : Set D) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Submodule_fg_and_span_eq_top_ofFiniteIdele.solution
