import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_isUnit_mul_prod_eq_of_sub_prod_linear_mem_pow

set_option autoImplicit false

universe u v

open MvPowerSeries

theorem MvPowerSeries.exists_isUnit_mul_prod_eq_of_sub_prod_linear_mem_pow
    {κ : Type u} [Field κ] {ι : Type v} [Fintype ι]
    (a b : ι → κ) (hab : ∀ i j : ι, i ≠ j → a i * b j - a j * b i ≠ 0)
    (f : MvPowerSeries (Fin 2) κ)
    (hf : f - ∏ i, (C (a i) * X 0 + C (b i) * X 1) ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ (Fintype.card ι + 1)) :
    ∃ (L : ι → MvPowerSeries (Fin 2) κ) (w : MvPowerSeries (Fin 2) κ), IsUnit w ∧
      (∀ i, L i - (C (a i) * X 0 + C (b i) * X 1) ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ 2) ∧
      f = w * ∏ i, L i := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_isUnit_mul_prod_eq_of_sub_prod_linear_mem_pow.solution
