import Definitions.Def_AutomorphicForm_ArchLowestWeight
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isArchLowestWeightAt_iff_and_isArchHolomorphicAt_iff_lower_eq_zero_of_hasArchCharacterAt
attribute [-simp] AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Manifold

theorem AutomorphicForm.isArchLowestWeightAt_iff_and_isArchHolomorphicAt_iff_lower_eq_zero_of_hasArchCharacterAt
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (k : ℤ) (c₀ : ℂ)
    (hk : HasArchCharacterAt₀ F w (archWeightCharAt hw k) φ)
    (hc : ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
      φ (adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ c₀) * φ g) :
    (IsArchLowestWeightAt w hw φ ↔
      IsArchSmoothAt hw φ ∧
        archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) = 0) ∧
    (IsArchHolomorphicAt w hw φ ↔
      IsArchSmoothAt hw φ ∧
        archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) = 0 ∧
        ((k : ℂ) + c₀ - 2) • φ = 0) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isArchLowestWeightAt_iff_and_isArchHolomorphicAt_iff_lower_eq_zero_of_hasArchCharacterAt.solution
