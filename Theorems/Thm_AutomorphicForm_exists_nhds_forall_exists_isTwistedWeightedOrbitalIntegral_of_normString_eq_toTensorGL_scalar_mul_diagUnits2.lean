import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_nhds_forall_exists_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_scalar_mul_diagUnits2

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_nhds_forall_exists_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_scalar_mul_diagUnits2
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) (ha : (a : v.adicCompletion K) ≠ 1)
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : AutomorphicForm.IsSemiLocalTestFn K L v φv) :
    ∃ W ∈ nhds (1 : v.adicCompletion K), ∀ ε : (v.adicCompletion K)ˣ, (ε : v.adicCompletion K) ∈ W →
      ∀ (b : (v.adicCompletion K)ˣ) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
        AutomorphicForm.normString K L (v.adicCompletion K) σ δ =
          AutomorphicForm.toTensorGL K L (v.adicCompletion K)
            (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1) →
        ∀ (τ' : Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)),
          τ'.IsHaarMeasure → τ' (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1 →
        ∀ J : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ δ τ' φv J →
          ∃ δ' : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
            AutomorphicForm.normString K L (v.adicCompletion K) σ δ' =
              AutomorphicForm.toTensorGL K L (v.adicCompletion K)
                (Matrix.GeneralLinearGroup.scalar (Fin 2) (b * ε) * diagUnits2 a 1) ∧
            ∃ τ'' : Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ'),
              τ''.IsHaarMeasure ∧ τ'' (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1 ∧
              AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ δ' τ'' φv J := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_nhds_forall_exists_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_scalar_mul_diagUnits2.solution
