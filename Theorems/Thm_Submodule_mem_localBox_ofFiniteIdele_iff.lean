import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_Submodule_mem_localBox_ofFiniteIdele_iff

set_option autoImplicit false

open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField

theorem Submodule.mem_localBox_ofFiniteIdele_iff
    {D : Type*} [Ring D] [Algebra ℚ D] (Λ : Submodule ℤ D)
    (hfg : Λ.FG) (hsp : Submodule.span ℚ (Λ : Set D) = ⊤)
    (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (x : D ⊗[ℚ] v.adicCompletion ℚ) :
    x ∈ Submodule.localBox (Submodule.ofFiniteIdele Λ g) v ↔
      ∃ y ∈ Submodule.localBox Λ v,
        x = Submodule.finiteAdeleEvalAt D v (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * y := by p2m_exact_reverting @_root_.P2MW.S_Submodule_mem_localBox_ofFiniteIdele_iff.solution
