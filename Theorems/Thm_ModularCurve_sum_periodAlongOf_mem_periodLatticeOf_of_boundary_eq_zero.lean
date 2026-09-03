import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import P2M.Util
import P2M.Sol.S_ModularCurve_sum_periodAlongOf_mem_periodLatticeOf_of_boundary_eq_zero

open UpperHalfPlane
open scoped MatrixGroups

set_option autoImplicit false
open Classical in

theorem ModularCurve.sum_periodAlongOf_mem_periodLatticeOf_of_boundary_eq_zero
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (Z : (ℍ × ℍ) →₀ ℤ)
    (hZ : ∀ τ : ℍ,
      Z.sum (fun e m =>
        (if ∃ γ : Γ, (γ : SL(2, ℤ)) • e.2 = τ then m else 0) -
        (if ∃ γ : Γ, (γ : SL(2, ℤ)) • e.1 = τ then m else 0)) = 0) :
    (Z.sum fun e m => m • ModularCurve.periodAlongOf Γ e.1 e.2) ∈
      ModularCurve.periodLatticeOf Γ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sum_periodAlongOf_mem_periodLatticeOf_of_boundary_eq_zero.solution
