import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import P2M.Util
import P2M.Sol.S_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_mem_of_mem_smul_normOneUnits_of_congr_mul_inv_mem

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm.AdelicTracePushforward
open scoped ENNReal
open scoped TensorProduct.RightActions in
attribute [local instance] AutomorphicForm.TransversalMeasure.semiLocalUnitsBorel
  AutomorphicForm.TransversalMeasure.archUnitsBorel in

theorem AutomorphicForm.TwistedBruhat.exists_isCompact_forall_mem_of_mem_smul_normOneUnits_of_congr_mul_inv_mem
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (π : (L ⊗[K] v.adicCompletion K)ˣ)
    (C : Set (L ⊗[K] v.adicCompletion K)ˣ) (hC : IsCompact C) :
    ∃ B : Set (L ⊗[K] v.adicCompletion K)ˣ, IsCompact B ∧
      ∀ x : (L ⊗[K] v.adicCompletion K)ˣ,
        π⁻¹ * x ∈ AutomorphicForm.TransversalMeasure.normOneUnits K L v →
        Units.mapEquiv (Algebra.TensorProduct.congr σ
            (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toMulEquiv x * x⁻¹ ∈ C →
        x ∈ B := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_mem_of_mem_smul_normOneUnits_of_congr_mul_inv_mem.solution
