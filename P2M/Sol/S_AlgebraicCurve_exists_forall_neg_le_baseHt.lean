import Definitions.Def_ModularCurve_JZeroHeightForm
import Theorems.Thm_AlgebraicCurve_exists_forall_neg_le_pairHt
import P2M.Util
namespace P2MW.S_AlgebraicCurve_exists_forall_neg_le_baseHt

set_option autoImplicit false

open AlgebraicCurve

theorem solution {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
    {r : ℕ} (s : Fin r → F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b v : Place (AlgebraicClosure ℚ) F, -C ≤ baseHt s b v := by
  classical
  obtain ⟨C, hC0, hC⟩ := AlgebraicCurve.exists_forall_neg_le_pairHt s
  refine ⟨C, hC0, fun b v => ?_⟩
  unfold baseHt
  split_ifs with h
  · linarith
  · exact hC v b
