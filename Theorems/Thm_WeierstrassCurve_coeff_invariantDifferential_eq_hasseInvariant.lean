module

public import Mathlib
public import Definitions.Def_WeierstrassCurve_HasseInvariant
public import P2M.Util
public import P2M.Sol.S_WeierstrassCurve_coeff_invariantDifferential_eq_hasseInvariant

@[expose] public section
attribute [-simp] ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

theorem WeierstrassCurve.coeff_invariantDifferential_eq_hasseInvariant
    {R : Type*} [CommRing R] (q : ℕ) [Fact q.Prime] [CharP R q] (hq : q ≠ 2)
    (W : WeierstrassCurve R) (x y ω : LaurentSeries R)
    (heq : y ^ 2 + HahnSeries.C W.a₁ * x * y + HahnSeries.C W.a₃ * y
      = x ^ 3 + HahnSeries.C W.a₂ * x ^ 2 + HahnSeries.C W.a₄ * x + HahnSeries.C W.a₆)
    (hx2 : x.coeff (-2) = 1) (hx : ∀ n < -2, x.coeff n = 0)
    (hy3 : y.coeff (-3) = -1) (hy : ∀ n < -3, y.coeff n = 0)
    (hω : ω * (2 * y + HahnSeries.C W.a₁ * x + HahnSeries.C W.a₃) = LaurentSeries.derivative R x) :
    ω.coeff ((q : ℤ) - 1) = W.hasseInvariant q := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_coeff_invariantDifferential_eq_hasseInvariant.solution
