import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_admissible_gl3CyclicSubspace_dualWhittakerFn3_rightTranslate

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

theorem LanglandsTunnell.CubicInduction.admissible_gl3CyclicSubspace_dualWhittakerFn3_rightTranslate
    (v : HeightOneSpectrum (𝓞 ℚ))
    (W : LocalGL3 v → ℂ)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (g₃ : LocalGL3 v) :
    (∃ Ud : Subgroup (LocalGL3 v), IsOpen (Ud : Set (LocalGL3 v)) ∧
      ∀ k ∈ Ud, ∀ y : LocalGL3 v,
        dualWhittakerFn3 (fun x => W (x * g₃)) (y * k) = dualWhittakerFn3 (fun x => W (x * g₃)) y) ∧
    (∀ Ud : Subgroup (LocalGL3 v), IsOpen (Ud : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace (dualWhittakerFn3 (fun x => W (x * g₃))),
        (∀ k ∈ Ud, ∀ y : LocalGL3 v, F (y * k) = F y) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) ∧
    (∀ ψv : AddChar (v.adicCompletion ℚ) ℂ, IsGL3PsiWhittakerFn ψv W →
      IsGL3PsiWhittakerFn ψv⁻¹ (dualWhittakerFn3 (fun x => W (x * g₃)))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_admissible_gl3CyclicSubspace_dualWhittakerFn3_rightTranslate.solution
