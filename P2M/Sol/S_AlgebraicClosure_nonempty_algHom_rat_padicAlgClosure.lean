import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicClosure_nonempty_algHom_rat_padicAlgClosure

theorem solution (p : ℕ) [Fact p.Prime] :
    Nonempty (AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]) := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    (AlgebraicClosure.instIsAlgClosure ℚ).isAlgebraic
  exact ⟨IsAlgClosed.lift⟩
