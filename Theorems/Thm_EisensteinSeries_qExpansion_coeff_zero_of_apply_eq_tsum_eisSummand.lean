import Mathlib
import P2M.Util
import P2M.Sol.S_EisensteinSeries_qExpansion_coeff_zero_of_apply_eq_tsum_eisSummand

set_option autoImplicit false

open scoped MatrixGroups ModularForm Real
open Complex

theorem EisensteinSeries.qExpansion_coeff_zero_of_apply_eq_tsum_eisSummand
    (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k) (v : Fin 2 → ZMod N)
    (G : ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) (k : ℤ))
    (hG : ∀ τ : UpperHalfPlane,
      G τ = ∑' x : {x : Fin 2 → ℤ // ((↑) : ℤ → ZMod N) ∘ x = v}, EisensteinSeries.eisSummand (k : ℤ) x.1 τ) :
    (UpperHalfPlane.qExpansion (N : ℝ) (⇑G)).coeff 0 =
      if v 0 = 0 then ∑' n : ℤ, 1 / ((((v 1).val : ℕ) : ℂ) + (N : ℂ) * (n : ℂ)) ^ k else 0 := by p2m_exact_reverting @_root_.P2MW.S_EisensteinSeries_qExpansion_coeff_zero_of_apply_eq_tsum_eisSummand.solution
