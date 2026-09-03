import Mathlib
import Definitions.Def_ModularCurve_KroneckerTransport
import P2M.Util
import P2M.Sol.S_ModularCurve_existsUnique_kroneckerRemainder

open Polynomial ModularCurve
theorem ModularCurve.existsUnique_kroneckerRemainder (p : ℕ) [Fact p.Prime]
    (data : ModularPolynomialData p) (hK : KroneckerCongruence p data) :
    ∃! R : Polynomial (Polynomial ℤ),
      data.Φ = (C X ^ p - X) * (C X - X ^ p) + C (C (p : ℤ)) * R := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_existsUnique_kroneckerRemainder.solution
