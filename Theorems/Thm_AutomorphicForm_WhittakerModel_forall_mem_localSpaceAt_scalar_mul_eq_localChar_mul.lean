import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.MellinTransform
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange

import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_AutomorphicForm_WhittakerModel_forall_mem_localSpaceAt_scalar_mul_eq_localChar_mul

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open scoped nonZeroDivisors

theorem AutomorphicForm.WhittakerModel.forall_mem_localSpaceAt_scalar_mul_eq_localChar_mul
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (x : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * x) = ((ξ z : ℂˣ) : ℂ) * φ x)
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ pins ψ p φ,
      ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        W (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((localChar ξ p z : ℂˣ) : ℂ) * W g := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_WhittakerModel_forall_mem_localSpaceAt_scalar_mul_eq_localChar_mul.solution
