import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Definitions.Def_ArtinL_Abelian
import P2M.Util
import P2M.Sol.S_Matrix_charpolyRev_mul_prod_pow_eq_prod_pow_of_forall_trace_pow_eq

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem Matrix.charpolyRev_mul_prod_pow_eq_prod_pow_of_forall_trace_pow_eq
    {K : Type*} [Field K] [CharZero K] {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m K) {k : ℕ} (E : Fin k → Polynomial K) (hE : ∀ i, (E i).coeff 0 = 1)
    (a : Fin k → ℤ)
    (h : ∀ j : ℕ, 0 < j → (M ^ j).trace =
      ∑ i, (a i : K) * PowerSeries.coeff j
        (((-(Polynomial.X * Polynomial.derivative (E i)) : Polynomial K) : PowerSeries K) *
          ((E i : Polynomial K) : PowerSeries K)⁻¹)) :
    M.charpolyRev * ∏ i, E i ^ (-a i).toNat = ∏ i, E i ^ (a i).toNat := by p2m_exact_reverting @_root_.P2MW.S_Matrix_charpolyRev_mul_prod_pow_eq_prod_pow_of_forall_trace_pow_eq.solution
