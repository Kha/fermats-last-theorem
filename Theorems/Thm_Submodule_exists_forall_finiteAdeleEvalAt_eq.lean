import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_Submodule_exists_forall_finiteAdeleEvalAt_eq

open scoped TensorProduct
open IsDedekindDomain NumberField

theorem Submodule.exists_forall_finiteAdeleEvalAt_eq
    {D : Type*} [Ring D] [Algebra ℚ D]
    (Λ : Submodule ℤ D) (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤)
    (x : (v : HeightOneSpectrum (𝓞 ℚ)) → D ⊗[ℚ] v.adicCompletion ℚ)
    (hx : ∀ᶠ v in Filter.cofinite, x v ∈ Submodule.localBox Λ v) :
    ∃ y : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ,
      ∀ v : HeightOneSpectrum (𝓞 ℚ), Submodule.finiteAdeleEvalAt D v y = x v := by p2m_exact_reverting @_root_.P2MW.S_Submodule_exists_forall_finiteAdeleEvalAt_eq.solution
