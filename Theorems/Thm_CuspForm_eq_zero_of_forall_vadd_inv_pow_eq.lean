import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_CuspForm_eq_zero_of_forall_vadd_inv_pow_eq

open CongruenceSubgroup ModularForm
open scoped ModularForm UpperHalfPlane MatrixGroups
theorem CuspForm.eq_zero_of_forall_vadd_inv_pow_eq
    {R q' : ℕ} [NeZero R] (hq' : 1 < q') (k : ℤ)
    (y : CuspForm ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (h : ∀ (j : ℕ) (τ : ℍ), y ((((q' : ℝ) ^ j)⁻¹) +ᵥ τ) = y τ) :
    y = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_eq_zero_of_forall_vadd_inv_pow_eq.solution
