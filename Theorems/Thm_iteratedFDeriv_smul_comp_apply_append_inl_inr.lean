import Mathlib
import P2M.Util
import P2M.Sol.S_iteratedFDeriv_smul_comp_apply_append_inl_inr

set_option autoImplicit false

theorem iteratedFDeriv_smul_comp_apply_append_inl_inr
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (A : E → F) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (j l : ℕ) (e : E) (ρ : ℝ) (u : Fin j → E) :
    iteratedFDeriv ℝ (j + l) (fun p : E × ℝ => φ p.2 • A p.1) (e, ρ)
        (Fin.append (fun i => ((u i, 0) : E × ℝ)) (fun _ : Fin l => ((0, 1) : E × ℝ))) =
      iteratedDeriv l φ ρ • iteratedFDeriv ℝ j A e u := by p2m_exact_reverting @_root_.P2MW.S_iteratedFDeriv_smul_comp_apply_append_inl_inr.solution
