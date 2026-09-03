import Mathlib
import P2M.Util
import P2M.Sol.S_LaurentSeries_exists_basis_forall_coeff_mem_valuationSubring_and_coeff_eq_ite

set_option autoImplicit false

theorem LaurentSeries.exists_basis_forall_coeff_mem_valuationSubring_and_coeff_eq_ite
    {F : Type*} [Field F] (O : ValuationSubring F) [IsDiscreteValuationRing O]
    (V : Submodule F (LaurentSeries F)) [FiniteDimensional F V]
    (hbdd : ∀ f ∈ V, ∃ c : F, c ≠ 0 ∧ ∀ n : ℤ, c * (f : LaurentSeries F).coeff n ∈ O) :
    ∃ (b : Module.Basis (Fin (Module.finrank F V)) F V) (p : Fin (Module.finrank F V) → ℤ),
      (∀ (i : Fin (Module.finrank F V)) (n : ℤ), ((b i : V) : LaurentSeries F).coeff n ∈ O) ∧
      ∀ i j : Fin (Module.finrank F V),
        ((b j : V) : LaurentSeries F).coeff (p i) = if i = j then 1 else 0 := by p2m_exact_reverting @_root_.P2MW.S_LaurentSeries_exists_basis_forall_coeff_mem_valuationSubring_and_coeff_eq_ite.solution
