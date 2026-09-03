import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isCompact_forall_ratio_mem_of_isTwistedWeightedOrbitalIntegralOn_infiniteAdeleRing_of_normString_eq_toTensorGL_scalar_mul_diagUnits2

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isCompact_forall_ratio_mem_of_isTwistedWeightedOrbitalIntegralOn_infiniteAdeleRing_of_normString_eq_toTensorGL_scalar_mul_diagUnits2
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (wt : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ)
    (φ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ) (hφ : HasCompactSupport φ) :
    ∃ C : Set (InfiniteAdeleRing K)ˣ, IsCompact C ∧
      ∀ (a b : (InfiniteAdeleRing K)ˣ) (δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
        AutomorphicForm.normString K L (InfiniteAdeleRing K) σ δ =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K)
            (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1) →
        ∀ (τ' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)) (J : ℂ),
          AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ μ wt δ τ' φ J →
            J ≠ 0 → a ∈ C := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isCompact_forall_ratio_mem_of_isTwistedWeightedOrbitalIntegralOn_infiniteAdeleRing_of_normString_eq_toTensorGL_scalar_mul_diagUnits2.solution
