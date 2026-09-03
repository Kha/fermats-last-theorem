import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_godementInner3_mulShift_polyGauss3_continuousOn_and_decay

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.CubicInduction.godementInner3_mulShift_polyGauss3_continuousOn_and_decay
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3) :
    ContinuousOn
        (fun p : ℝ × Matrix (Fin 2) (Fin 2) ℝ =>
          godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal p.1)) S p.2 1)
        {p | p.2.det ≠ 0} ∧
      ∀ N : ℕ, ∃ C : ℝ, ∃ A : ℕ, 0 ≤ C ∧
        ∀ (e : Matrix (Fin 2) (Fin 2) ℝ) (y : ℝ), e.det ≠ 0 →
          ‖godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S e 1‖ ≤
            C * |e.det|⁻¹ * Real.exp (-(Real.pi * ∑ i, ∑ j, e i j ^ 2)) * (1 + ∑ i, ∑ j, e i j ^ 2) ^ A *
              ((1 + y ^ 2 * ∑ i, (e⁻¹ 1 i) ^ 2) ^ N)⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_godementInner3_mulShift_polyGauss3_continuousOn_and_decay.solution
