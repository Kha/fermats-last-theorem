import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_measurableEquiv_measurePreserving_pi_apply_succ_eq_inv_mul_mul

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_measurableEquiv_measurePreserving_pi_apply_succ_eq_inv_mul_mul
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] {n : ℕ} (D : Fin (n + 1) → G) :
    ∃ Θ : (Fin (n + 1) → G) ≃ᵐ (Fin (n + 1) → G),
      MeasurePreserving Θ (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) ∧
      ∀ x : Fin (n + 1) → G, Θ x 0 = x 0 ∧
        ∀ k : Fin n, Θ x k.succ = (x k.castSucc)⁻¹ * D k.castSucc * x k.succ := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_measurableEquiv_measurePreserving_pi_apply_succ_eq_inv_mul_mul.solution
