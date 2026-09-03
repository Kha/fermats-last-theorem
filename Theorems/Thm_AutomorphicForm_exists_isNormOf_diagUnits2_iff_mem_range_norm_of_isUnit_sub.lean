import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isNormOf_diagUnits2_iff_mem_range_norm_of_isUnit_sub
attribute [-simp] LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_isNormOf_diagUnits2_iff_mem_range_norm_of_isUnit_sub
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (A : Type) [CommRing A] [Algebra K A] (x y : Aˣ) (hxy : IsUnit ((x : A) - (y : A))) :
    (∃ δ : GL (Fin 2) (L ⊗[K] A), AutomorphicForm.IsNormOf K L A σ (diagUnits2 x y) δ) ↔
      ((x : A) ∈ Set.range (fun t : (L ⊗[K] A)ˣ => Algebra.norm A (t : L ⊗[K] A)) ∧
       (y : A) ∈ Set.range (fun t : (L ⊗[K] A)ˣ => Algebra.norm A (t : L ⊗[K] A))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isNormOf_diagUnits2_iff_mem_range_norm_of_isUnit_sub.solution
