import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.MellinTransform
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import P2M.Util
import P2M.Sol.S_AutomorphicForm_archReflectLower_archReflectLower_eq_smul_of_hasArchCharacterAt_one_of_archCasimirAt_eq_smul

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace LanglandsTunnell.RealArchParam
open scoped nonZeroDivisors

theorem AutomorphicForm.archReflectLower_archReflectLower_eq_smul_of_hasArchCharacterAt_one_of_archCasimirAt_eq_smul
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal) (lam : ℂ)
    (x : AdelicGL2 (𝓞 F) F → ℂ)
    (_hsm : IsArchSmoothAt hw x)
    (_hwt : HasArchCharacterAt₀ F w (archWeightCharAt hw 1) x)
    (_hcas : archCasimirAt hw x = lam • x) :
    let T : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) := fun y g =>
      (archDerivAt hw ArchDir.H y - Complex.I • (archDerivAt hw ArchDir.E y + archDerivAt hw ArchDir.Fm y))
        (g * archRealGLAt hw UpperHalfPlane.J)
    T (T x) = (1 - 4 * lam) • x ∧

    ∀ κ : ℂ, κ ^ 2 * (1 - 4 * lam) = 1 →
      ∀ g : AdelicGL2 (𝓞 F) F,
        (x + κ • T x) (g * archRealGLAt hw UpperHalfPlane.J)
          = κ * (archDerivAt hw ArchDir.H (x + κ • T x)
                  - Complex.I • (archDerivAt hw ArchDir.E (x + κ • T x) + archDerivAt hw ArchDir.Fm (x + κ • T x))) g := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_archReflectLower_archReflectLower_eq_smul_of_hasArchCharacterAt_one_of_archCasimirAt_eq_smul.solution
