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
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isTwistedOrbitalIntegral_scalar_mul_of_isTwistedOrbitalIntegral_comp_scalar_mul

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.isTwistedOrbitalIntegral_scalar_mul_of_isTwistedOrbitalIntegral_comp_scalar_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (c : (L ⊗[K] v.adicCompletion K)ˣ)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (hτ'1 : τ' (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (τ'' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ))
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ)))
    (hτ'' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ)) τ'')
    (hτ''1 : τ'' (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (I : ℂ)
    (hI : AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ'
      (fun x => φv (Matrix.GeneralLinearGroup.scalar (Fin 2) c * x)) I) :
    AutomorphicForm.IsTwistedOrbitalIntegral K L v σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ) τ'' φv I := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isTwistedOrbitalIntegral_scalar_mul_of_isTwistedOrbitalIntegral_comp_scalar_mul.solution
