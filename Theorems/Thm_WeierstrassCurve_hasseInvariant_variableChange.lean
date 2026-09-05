module

public import Mathlib
public import Definitions.Def_WeierstrassCurve_HasseInvariant
public import Definitions.Def_Polynomial_DeuringPolynomial
public import P2M.Util
public import P2M.Sol.S_WeierstrassCurve_hasseInvariant_variableChange

@[expose] public section

open Polynomial WeierstrassCurve
theorem WeierstrassCurve.hasseInvariant_variableChange {R : Type*} [CommRing R] {q : ℕ} [Fact q.Prime]
    [CharP R q] (W : WeierstrassCurve R) (v : VariableChange R) :
    (v • W).hasseInvariant q = ((v.u⁻¹ : Rˣ) : R) ^ (q - 1) * W.hasseInvariant q := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_hasseInvariant_variableChange.solution
