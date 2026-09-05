module

public import Mathlib
public import Definitions.Def_WeierstrassCurve_HasseInvariant
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero

@[expose] public section

open Polynomial WeierstrassCurve
theorem WeierstrassCurve.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) [CharP K q] (W : WeierstrassCurve K) [W.IsElliptic] : (∀ P : W.toAffine.Point, q • P = 0 → P = 0) ↔ W.hasseInvariant q = 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero.solution
