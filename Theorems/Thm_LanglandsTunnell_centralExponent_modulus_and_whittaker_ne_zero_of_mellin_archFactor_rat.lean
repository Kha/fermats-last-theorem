import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_ConverseData
import Mathlib.Analysis.MellinTransform
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_centralExponent_modulus_and_whittaker_ne_zero_of_mellin_archFactor_rat
attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

theorem LanglandsTunnell.centralExponent_modulus_and_whittaker_ne_zero_of_mellin_archFactor_rat
    (Θ : HeckeEigensystem ℚ ℂ) (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (σ₀ : ℝ)
    (hσ₀ : ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      ‖((ξ.comp Subgroup.topEquiv.symm.toMonoidHom x : ℂˣ) : ℂ)‖ = TateGlobal.ideleNorm ℚ x ^ σ₀)
    (A : RealArchParam)
    (hcen : LanglandsTunnell.Converse.IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) (default : InfinitePlace ℚ)
      (A.centralExponent + 1) (A.centralSign.val : ℤ))
    (par : ZMod 2) (φ₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wr : InfinitePlace ℚ → ℂ → ℂ)
    (C : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hC : C 1 1 ≠ 0)
    (hfac : (∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
                whittakerCoefficient ℚ
                    (productionPinsGeneral ℚ)
                    NumberField.StandardAddChar.psiQ φ₀ 1 (diagOne a * g)
                  = (∏ w : InfinitePlace ℚ, Wr w (NumberField.InfinitePlace.Completion.extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
                      * C (a : AdeleRing (𝓞 ℚ) ℚ).2 g))
    (hMel : ∀ b : ZMod 2, (b = par ∨ b = par + A.centralSign) →
      ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
        MellinConvergent (fun t : ℝ => (Wr default t + (-1 : ℂ) ^ b.val * Wr default (-t)) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (Wr default t + (-1 : ℂ) ^ b.val * Wr default (-t)) / (t : ℂ)) s
            = (A.twist 0 b).archFactor s) :
    σ₀ = (A.centralExponent + 1).re ∧
    (∀ z : ℝˣ, ‖(TateGlobal.archLocalChar (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) default
        (Units.map (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
          (IsTotallyReal.isReal (default : InfinitePlace ℚ))).symm.toMonoidHom z) : ℂ)‖ = |(z : ℝ)| ^ σ₀) ∧
    (∃ t : ℝˣ, Wr default ((t : ℝ) : ℂ) ≠ 0) ∧
    whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₀ 1 ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_centralExponent_modulus_and_whittaker_ne_zero_of_mellin_archFactor_rat.solution
