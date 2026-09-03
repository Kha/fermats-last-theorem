import Mathlib
import P2M.Util
import P2M.Sol.S_EisensteinSeries_qExpansion_coeff_of_apply_eq_tsum_eisSummand

set_option autoImplicit false

open scoped MatrixGroups ModularForm Real
open Complex

theorem EisensteinSeries.qExpansion_coeff_of_apply_eq_tsum_eisSummand
    (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k) (v : Fin 2 → ZMod N)
    (G : ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) (k : ℤ))
    (hG : ∀ τ : UpperHalfPlane,
      G τ = ∑' x : {x : Fin 2 → ℤ // ((↑) : ℤ → ZMod N) ∘ x = v}, EisensteinSeries.eisSummand (k : ℤ) x.1 τ)
    (n : ℕ) (hn : 1 ≤ n) :
    (UpperHalfPlane.qExpansion (N : ℝ) (⇑G)).coeff n =
      ((-2 * π * I) ^ k / ((k - 1).factorial * (N : ℂ) ^ k)) *
        ∑ md ∈ Nat.divisorsAntidiagonal n,
          (md.2 : ℂ) ^ (k - 1) *
            ((if ((md.1 : ℕ) : ZMod N) = v 0 then Complex.exp (2 * π * I * ((md.2 * (v 1).val : ℕ) : ℂ) / N) else 0) +
              (-1) ^ k * (if ((md.1 : ℕ) : ZMod N) = -v 0 then Complex.exp (-(2 * π * I * ((md.2 * (v 1).val : ℕ) : ℂ) / N)) else 0)) := by p2m_exact_reverting @_root_.P2MW.S_EisensteinSeries_qExpansion_coeff_of_apply_eq_tsum_eisSummand.solution
