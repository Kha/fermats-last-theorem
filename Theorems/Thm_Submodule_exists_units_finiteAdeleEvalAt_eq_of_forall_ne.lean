import Mathlib
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_Submodule_exists_units_finiteAdeleEvalAt_eq_of_forall_ne

set_option autoImplicit false

open scoped TensorProduct
open IsDedekindDomain NumberField

theorem Submodule.exists_units_finiteAdeleEvalAt_eq_of_forall_ne
    {D : Type*} [Ring D] [Algebra ℚ D] [Module.Finite ℚ D] (Λ : Submodule ℤ D) (hfg : Λ.FG)
    (hspan : Submodule.span ℚ (Λ : Set D) = ⊤) (v : HeightOneSpectrum (𝓞 ℚ))
    (y yi : D ⊗[ℚ] v.adicCompletion ℚ) (hy : y * yi = 1) (hy' : yi * y = 1)
    (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hg : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt D w (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.localBox Λ w ∧
      Submodule.finiteAdeleEvalAt D w ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.localBox Λ w) :
    ∃ h : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      Submodule.finiteAdeleEvalAt D v (h : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = y ∧
      Submodule.finiteAdeleEvalAt D v ((h⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = yi ∧
      ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
        Submodule.finiteAdeleEvalAt D w (h : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          Submodule.finiteAdeleEvalAt D w (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∧
        Submodule.finiteAdeleEvalAt D w ((h⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          Submodule.finiteAdeleEvalAt D w ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) := by p2m_exact_reverting @_root_.P2MW.S_Submodule_exists_units_finiteAdeleEvalAt_eq_of_forall_ne.solution
