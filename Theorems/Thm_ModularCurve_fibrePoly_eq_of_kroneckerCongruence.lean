module

public import Mathlib
public import Definitions.Def_ModularCurve_FibrePoly
import P2M.Util
import P2M.Sol.S_ModularCurve_fibrePoly_eq_of_kroneckerCongruence

@[expose] public section

open Polynomial
theorem ModularCurve.fibrePoly_eq_of_kroneckerCongruence {k : Type*} [Field k]
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] (data : ModularCurve.ModularPolynomialData ℓ)
    (hK : ModularCurve.KroneckerCongruence ℓ data) (a : k) :
    ModularCurve.fibrePoly data.Φ a =
      (Polynomial.C (a ^ ℓ) - Polynomial.X) * (Polynomial.C a - Polynomial.X ^ ℓ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_fibrePoly_eq_of_kroneckerCongruence.solution
