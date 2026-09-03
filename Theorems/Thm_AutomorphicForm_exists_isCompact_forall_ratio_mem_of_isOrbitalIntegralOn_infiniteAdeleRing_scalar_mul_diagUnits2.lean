import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isCompact_forall_ratio_mem_of_isOrbitalIntegralOn_infiniteAdeleRing_scalar_mul_diagUnits2

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isCompact_forall_ratio_mem_of_isOrbitalIntegralOn_infiniteAdeleRing_scalar_mul_diagUnits2
    (K : Type) [Field K] [NumberField K]
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : HasCompactSupport fa) :
    ∃ C : Set (InfiniteAdeleRing K)ˣ, IsCompact C ∧
      ∀ (a b : (InfiniteAdeleRing K)ˣ)
        (τ : Measure (Subgroup.centralizer
            ({Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1} : Set (GL (Fin 2) (InfiniteAdeleRing K)))))
        (J : ℂ),
        AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) ν
            (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1) τ fa J → J ≠ 0 → a ∈ C := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isCompact_forall_ratio_mem_of_isOrbitalIntegralOn_infiniteAdeleRing_scalar_mul_diagUnits2.solution
