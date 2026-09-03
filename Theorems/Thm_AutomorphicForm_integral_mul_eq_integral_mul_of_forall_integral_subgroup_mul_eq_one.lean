import Mathlib.MeasureTheory.Integral.Bochner.Basic
import P2M.Util
import P2M.Sol.S_AutomorphicForm_integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]
    (T : Subgroup G) [MeasurableSpace T] [MeasurableInv T]
    (hT : Measurable (Subtype.val : T → G))
    (τ : Measure T) [SFinite τ] [τ.IsInvInvariant]
    (F : G → ℂ) (hF : Measurable F) (hFT : ∀ (t : T) (x : G), F ((t : G) * x) = F x)
    (w w' : G → ℝ) (hw : ∀ x, 0 ≤ w x) (hw' : ∀ x, 0 ≤ w' x)
    (hwm : Measurable w) (hw'm : Measurable w')
    (h1 : ∀ x, F x ≠ 0 → ∫ t : T, w ((t : G) * x) ∂τ = 1)
    (h1' : ∀ x, F x ≠ 0 → ∫ t : T, w' ((t : G) * x) ∂τ = 1) :
    ∫ x, F x * (w x : ℂ) ∂μ = ∫ x, F x * (w' x : ℂ) ∂μ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one.solution
