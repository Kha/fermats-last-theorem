import Mathlib
import Definitions.Def_ModularCurve_X1DegeneracyPullback
import P2M.Util
import P2M.Sol.S_ModularCurve_JOne_degeneracyPullbackPair_galois_smul

set_option autoImplicit false

theorem ModularCurve.JOne.degeneracyPullbackPair_galois_smul (N N' t : ℕ) [NeZero t] (i : Fin 2)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ModularCurve.JOne N) :
    ModularCurve.JOne.degeneracyPullbackPair N N' t i (σ • x) =
      σ • ModularCurve.JOne.degeneracyPullbackPair N N' t i x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JOne_degeneracyPullbackPair_galois_smul.solution
