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
import Definitions.Def_M4aHerbrand_ArchSemilocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_mem_of_mem_archNormOneUnits_of_placeEquivAlg_congr_mul_inv_mem

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

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

theorem AutomorphicForm.TwistedBruhat.exists_isCompact_forall_mem_of_mem_archNormOneUnits_of_placeEquivAlg_congr_mul_inv_mem
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : InfinitePlace K)
    (C : Set ((w : v.Extension L) → w.1.Completion)ˣ) (hC : IsCompact C) :
    ∃ B : Set ((w : v.Extension L) → w.1.Completion)ˣ, IsCompact B ∧
      ∀ x : ((w : v.Extension L) → w.1.Completion)ˣ,
        x ∈ AutomorphicForm.TransversalMeasure.archNormOneUnits K L v →
        M4aHerbrand.ArchSemilocal.placeEquivAlg (K := K) (L := L) v
            ((Algebra.TensorProduct.congr (AlgEquiv.refl : v.Completion ≃ₐ[v.Completion] v.Completion) σ)
              ((M4aHerbrand.ArchSemilocal.placeEquivAlg (K := K) (L := L) v).symm
                ((x : ((w : v.Extension L) → w.1.Completion)ˣ) : (w : v.Extension L) → w.1.Completion))) *
          (((x⁻¹ : ((w : v.Extension L) → w.1.Completion)ˣ)) : (w : v.Extension L) → w.1.Completion) ∈
          (Units.val : ((w : v.Extension L) → w.1.Completion)ˣ → ((w : v.Extension L) → w.1.Completion)) '' C →
        x ∈ B := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_mem_of_mem_archNormOneUnits_of_placeEquivAlg_congr_mul_inv_mem.solution
