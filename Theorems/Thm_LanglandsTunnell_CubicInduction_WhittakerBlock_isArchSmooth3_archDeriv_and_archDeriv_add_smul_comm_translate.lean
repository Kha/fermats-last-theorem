import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate :
    (∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 φ →
      ∀ i j : Fin 3, WhittakerBlock.IsArchSmooth3 (archDeriv i j φ)) ∧
    (∀ φ ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 φ → WhittakerBlock.IsArchSmooth3 ψ →
      ∀ i j : Fin 3, archDeriv i j (φ + ψ) = archDeriv i j φ + archDeriv i j ψ) ∧
    (∀ (c : ℂ) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ i j : Fin 3, archDeriv i j (c • φ) = c • archDeriv i j φ) ∧
    (∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 φ → ∀ i j k l : Fin 3,
      archDeriv i j (archDeriv k l φ) - archDeriv k l (archDeriv i j φ) =
        (if j = k then archDeriv i l φ else 0) - (if l = i then archDeriv k j φ else 0)) ∧
    (∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 φ → ∀ (y : AdelicGL 3 (𝓞 ℚ) ℚ),
      WhittakerBlock.IsArchSmooth3 (fun x => φ (x * y)) ∧
      ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3),
        archDeriv i j (fun x => φ (x * y)) g =
          ∑ p : Fin 3, ∑ q : Fin 3,
            ((((StandardKernel.realGL (archComponent3 (𝓞 ℚ) ℚ y))⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) p i *
              ((StandardKernel.realGL (archComponent3 (𝓞 ℚ) ℚ y) : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) j q : ℂ) *
            archDeriv p q φ (g * y)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.solution
