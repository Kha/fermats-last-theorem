import Mathlib
import Definitions.Def_EisensteinSeries_WeierstrassZeta
import P2M.Util
import P2M.Sol.S_EisensteinSeries_eisensteinG1_apply_smul_and_eisensteinG1_add

set_option autoImplicit false

open scoped Real MatrixGroups Matrix

theorem EisensteinSeries.eisensteinG1_apply_smul_and_eisensteinG1_add (N : ℕ) [NeZero N]
    (τ : UpperHalfPlane) :
    (∀ (γ : SL(2, ℤ)) (v : Fin 2 → ℤ),
        EisensteinSeries.eisensteinG1 N v (γ • τ) =
          UpperHalfPlane.denom γ τ *
            EisensteinSeries.eisensteinG1 N (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) τ) ∧
    (∀ v w : Fin 2 → ℤ, (¬ ∀ i, (N : ℤ) ∣ v i) →
        EisensteinSeries.eisensteinG1 N (v + (N : ℤ) • w) τ =
          EisensteinSeries.eisensteinG1 N v τ) := by p2m_exact_reverting @_root_.P2MW.S_EisensteinSeries_eisensteinG1_apply_smul_and_eisensteinG1_add.solution
