import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_Submodule_exists_units_forall_finiteAdeleEvalAt_eq_conjByFiniteIdele_eq

set_option autoImplicit false

open scoped TensorProduct
open IsDedekindDomain NumberField

theorem Submodule.exists_units_forall_finiteAdeleEvalAt_eq_conjByFiniteIdele_eq
    {D : Type*} [Ring D] [Algebra ℚ D]
    (Λ Λ' : Submodule ℤ D) (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤)
    (hfg' : Λ'.FG) (hspan' : Submodule.span ℚ (Λ' : Set D) = ⊤)
    (g : ∀ v : HeightOneSpectrum (𝓞 ℚ), (D ⊗[ℚ] v.adicCompletion ℚ)ˣ)
    (hfin : ∀ᶠ v in Filter.cofinite, g v ∈ Submodule.localBoxUnits Λ' v)
    (hconj : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (x : D ⊗[ℚ] v.adicCompletion ℚ),
      x ∈ Submodule.localBox Λ v ↔ ∃ y ∈ Submodule.localBox Λ' v,
        x = ((g v : (D ⊗[ℚ] v.adicCompletion ℚ)ˣ) : D ⊗[ℚ] v.adicCompletion ℚ) * y *
          (((g v)⁻¹ : (D ⊗[ℚ] v.adicCompletion ℚ)ˣ) : D ⊗[ℚ] v.adicCompletion ℚ)) :
    ∃ β : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ),
        Submodule.finiteAdeleEvalAt D v (β : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          ((g v : (D ⊗[ℚ] v.adicCompletion ℚ)ˣ) : D ⊗[ℚ] v.adicCompletion ℚ)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ),
        Submodule.finiteAdeleEvalAt D v ((β⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (((g v)⁻¹ : (D ⊗[ℚ] v.adicCompletion ℚ)ˣ) : D ⊗[ℚ] v.adicCompletion ℚ)) ∧
      Submodule.conjByFiniteIdele Λ' β = Λ := by p2m_exact_reverting @_root_.P2MW.S_Submodule_exists_units_forall_finiteAdeleEvalAt_eq_conjByFiniteIdele_eq.solution
