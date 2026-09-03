import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_AutomorphicForm_mem_range_idelicNorm_of_isNormOf_centralScalar_mul_globalPoints_diagUnits2_of_mem_range_norm
attribute [-simp] LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.mem_range_idelicNorm_of_isNormOf_centralScalar_mul_globalPoints_diagUnits2_of_mem_range_norm
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (a b : Kˣ) (hab : a ≠ b)
    (ha : (a : K) ∈ Set.range (Algebra.norm K : L → K))
    (z : (AdeleRing (𝓞 K) K)ˣ)
    (h : ∃ δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ
        (AutomorphicForm.centralScalar (𝓞 K) K z * AutomorphicForm.globalPoints (𝓞 K) K (diagUnits2 a b)) δ) :
    z ∈ Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_mem_range_idelicNorm_of_isNormOf_centralScalar_mul_globalPoints_diagUnits2_of_mem_range_norm.solution
