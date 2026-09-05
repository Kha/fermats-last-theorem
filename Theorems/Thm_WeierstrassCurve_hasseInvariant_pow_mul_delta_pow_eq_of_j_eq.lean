module

public import Mathlib
public import Definitions.Def_WeierstrassCurve_HasseInvariant
public import P2M.Util
public import P2M.Sol.S_WeierstrassCurve_hasseInvariant_pow_mul_delta_pow_eq_of_j_eq

@[expose] public section
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem WeierstrassCurve.hasseInvariant_pow_mul_delta_pow_eq_of_j_eq
    (q : ℕ) [Fact q.Prime]
    {F : Type*} [Field F] [CharP F q] [IsSepClosed F]
    (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic] (h : W.j = W'.j) :
    WeierstrassCurve.hasseInvariant q W ^ 12 * W'.Δ ^ (q - 1) =
      WeierstrassCurve.hasseInvariant q W' ^ 12 * W.Δ ^ (q - 1) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_hasseInvariant_pow_mul_delta_pow_eq_of_j_eq.solution
