import Definitions.Def_ModularCurve_JZeroHeightForm
import Theorems.Thm_ModularCurve_JZero_exists_absLogHeight_minors_le
import P2M.Util
namespace P2MW.S_AlgebraicCurve_exists_forall_neg_le_pairHt

set_option autoImplicit false

open AlgebraicCurve

theorem solution {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
    {r : ℕ} (s : Fin r → F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v w : Place (AlgebraicClosure ℚ) F, -C ≤ pairHt s v w := by
  obtain ⟨C₀, hC₀⟩ := ModularCurve.JZero.exists_absLogHeight_minors_le r
  refine ⟨max C₀ 0, le_max_right _ _, fun v w => ?_⟩
  have h := hC₀ (evalVec s v) (evalVec s w)
  have hch : chordVec s v w = fun p : Fin r × Fin r =>
      evalVec s v p.1 * evalVec s w p.2 - evalVec s v p.2 * evalVec s w p.1 := rfl
  have hmax : C₀ ≤ max C₀ 0 := le_max_left _ _
  simp only [pairHt, pointHt, hch]
  linarith
