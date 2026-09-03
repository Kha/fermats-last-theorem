import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_AutomorphicForm_AdelicLsXi
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_whittakerCoefficient_one_diagOne_ne_zero_of_glFin_eq_one_rat
attribute [-simp] AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
p2m_open "AutomorphicForm~eq_zero_of_forall_torusRay_eq_zero_of_mul_det_pos AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"

theorem AutomorphicForm.exists_whittakerCoefficient_one_diagOne_ne_zero_of_glFin_eq_one_rat
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hper : ∀ (β : ℚ) (u : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + u) * g) = φ (unipotentGL2 u * g))
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ)
    (hcent : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (centralScalar (𝓞 ℚ) ℚ z * g) = χ z * φ g)
    (n : ℤ) (hwt : HasArchCharacterAt₀ ℚ Rat.infinitePlace (archWeightCharAt Rat.isReal_infinitePlace n) φ)
    (x : AdelicGL2 (𝓞 ℚ) ℚ) (hx : glFin (𝓞 ℚ) ℚ x = 1)
    (hW : whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 x ≠ 0) :
    ∃ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, (a : AdeleRing (𝓞 ℚ) ℚ).2 = 1 ∧
      whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 (diagOne a) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_whittakerCoefficient_one_diagOne_ne_zero_of_glFin_eq_one_rat.solution
