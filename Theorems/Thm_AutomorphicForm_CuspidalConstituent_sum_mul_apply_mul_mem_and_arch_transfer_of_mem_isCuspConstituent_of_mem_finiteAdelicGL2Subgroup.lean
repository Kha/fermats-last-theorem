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
import P2M.Sol.S_AutomorphicForm_CuspidalConstituent_sum_mul_apply_mul_mem_and_arch_transfer_of_mem_isCuspConstituent_of_mem_finiteAdelicGL2Subgroup

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace LanglandsTunnell.RealArchParam
open scoped nonZeroDivisors

theorem AutomorphicForm.CuspidalConstituent.sum_mul_apply_mul_mem_and_arch_transfer_of_mem_isCuspConstituent_of_mem_finiteAdelicGL2Subgroup
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hV : CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ V)
    (hsmV : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∀ x ∈ V, IsArchSmoothAt hw x)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφV : φ ∈ V)
    (m : ℕ) (c : Fin m → ℂ) (g : Fin m → AdelicGL2 (𝓞 ℚ) ℚ) (hg : ∀ i, g i ∈ finiteAdelicGL2Subgroup ℚ) :
    let φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := fun x => ∑ i, c i * φ (x * g i)
    φ' ∈ V ∧
    (Continuous φ → Continuous φ') ∧
    (∀ tys : ArchTypeFamily ℚ, φ ∈ archCutSubmodule ℚ tys → φ' ∈ archCutSubmodule ℚ tys) ∧
    (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (n : ℤ),
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) φ → HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) φ') ∧
    (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (lam : ℂ),
      (IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = lam • φ) →
        (IsArchSmoothAt hw φ' ∧ archCasimirAt hw φ' = lam • φ')) ∧
    (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (e : ℂ),
      (∀ x : AdelicGL2 (𝓞 ℚ) ℚ, φ (x * archRealGLAt hw UpperHalfPlane.J) = e * φ x) →
        ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, φ' (x * archRealGLAt hw UpperHalfPlane.J) = e * φ' x) ∧
    (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (cJ : ℂ),
      (∀ x : AdelicGL2 (𝓞 ℚ) ℚ, φ (x * archRealGLAt hw UpperHalfPlane.J) = cJ * (archDerivAt hw ArchDir.H φ - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ)) x) →
        ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, φ' (x * archRealGLAt hw UpperHalfPlane.J) = cJ * (archDerivAt hw ArchDir.H φ' - Complex.I • (archDerivAt hw ArchDir.E φ' + archDerivAt hw ArchDir.Fm φ')) x) ∧
    (∀ (w : InfinitePlace ℚ) (hw : w.IsReal), (archDerivAt hw ArchDir.H φ - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ)) = 0 → (archDerivAt hw ArchDir.H φ' - Complex.I • (archDerivAt hw ArchDir.E φ' + archDerivAt hw ArchDir.Fm φ')) = 0) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_sum_mul_apply_mul_mem_and_arch_transfer_of_mem_isCuspConstituent_of_mem_finiteAdelicGL2Subgroup.solution
