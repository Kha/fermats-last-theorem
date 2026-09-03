import Mathlib
import Definitions.Def_ModularCurve_FibrePoly
import P2M.Util
import P2M.Sol.S_ModularCurve_roots_fibrePoly

open Polynomial
theorem ModularCurve.roots_fibrePoly {k : Type*} [Field k] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP k ℓ] [PerfectRing k ℓ] (data : ModularCurve.ModularPolynomialData ℓ)
    (hK : ModularCurve.KroneckerCongruence ℓ data) (a : k) :
    (ModularCurve.fibrePoly data.Φ a).roots =
      {a ^ ℓ} + ℓ • {(frobeniusEquiv k ℓ).symm a} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_roots_fibrePoly.solution
