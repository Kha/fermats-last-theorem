import Definitions.Def_ModularCurve_ComponentGroupKirchhoff
import Theorems.Thm_ModularCurve_natCard_componentGroup_eq_natAbs_det
import P2M.Util
namespace P2MW.S_ModularCurve_natCard_componentGroup_eq_natAbs_det_diffChar

open ModularCurve Module

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]
    {e : ι → ℕ} (he : ∀ x, 0 < e x) (σ : Option κ ≃ ι) :
    Nat.card (componentGroup e) = ((gramMatrixOf e (diffChar σ)).det).natAbs := by
  have h : gramMatrixOf e ⇑(diffBasisOf σ) = gramMatrixOf e (diffChar σ) := by
    ext i j
    rw [gramMatrixOf_apply, gramMatrixOf_apply, diffBasisOf_apply, diffBasisOf_apply]
  rw [← h]
  exact ModularCurve.natCard_componentGroup_eq_natAbs_det he (diffBasisOf σ)
