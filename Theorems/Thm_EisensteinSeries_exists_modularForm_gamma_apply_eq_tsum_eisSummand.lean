import Mathlib
import P2M.Util
import P2M.Sol.S_EisensteinSeries_exists_modularForm_gamma_apply_eq_tsum_eisSummand

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem EisensteinSeries.exists_modularForm_gamma_apply_eq_tsum_eisSummand
    (N : ℕ) [NeZero N] (k : ℤ) (hk : 3 ≤ k) :
    ∃ G : (Fin 2 → ZMod N) → ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) k,
      (∀ (v : Fin 2 → ZMod N) (τ : UpperHalfPlane),
        G v τ = ∑' x : {x : Fin 2 → ℤ // ((↑) : ℤ → ZMod N) ∘ x = v}, EisensteinSeries.eisSummand k x.1 τ) ∧
      (∀ (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)),
        ((⇑(G v) : UpperHalfPlane → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) =
          ⇑(G (Matrix.vecMul v ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N))))) := by p2m_exact_reverting @_root_.P2MW.S_EisensteinSeries_exists_modularForm_gamma_apply_eq_tsum_eisSummand.solution
