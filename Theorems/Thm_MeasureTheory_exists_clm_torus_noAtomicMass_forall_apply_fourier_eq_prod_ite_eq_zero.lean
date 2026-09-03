import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_ite_eq_zero

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_ite_eq_zero
    (d : ℕ) (hd : 1 ≤ d) :
    ∃ μ : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ,
      (∀ (τ : Fin d → AddCircle (1 : ℝ)), ∀ ε > (0 : ℝ),
        ∃ U : Fin d → Set (AddCircle (1 : ℝ)), (∀ i, IsOpen (U i) ∧ τ i ∈ U i) ∧
          ∀ g : C((Fin d → AddCircle (1 : ℝ)), ℂ),
            (∀ θ, (∃ i, θ i ∉ U i) → g θ = 0) → (∀ θ, ‖g θ‖ ≤ 1) → ‖μ g‖ < ε) ∧
      ∀ (n : Fin d → ℤ) (e : C((Fin d → AddCircle (1 : ℝ)), ℂ)),
        (∀ θ, e θ = ∏ i, fourier (n i) (θ i)) → μ e = ∏ i : Fin d, (if n i = 0 then (1 : ℂ) else 0) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_ite_eq_zero.solution
