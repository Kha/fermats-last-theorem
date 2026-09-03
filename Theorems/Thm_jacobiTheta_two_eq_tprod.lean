import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import P2M.Util
import P2M.Sol.S_jacobiTheta_two_eq_tprod
open scoped Real
open Complex
theorem jacobiTheta_two_eq_tprod (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta₂ z τ = ∏' n : ℕ,
      ((1 - Complex.exp (2 * π * I * (n + 1) * τ)) *
        (1 + Complex.exp (π * I * (2 * n + 1) * τ + 2 * π * I * z)) *
        (1 + Complex.exp (π * I * (2 * n + 1) * τ - 2 * π * I * z))) := by p2m_exact_reverting @_root_.P2MW.S_jacobiTheta_two_eq_tprod.solution
