import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_addOrderOf_reduceHom_of_natCast_ne_zero

open WeierstrassCurve IsLocalRing

theorem WeierstrassCurve.addOrderOf_reduceHom_of_natCast_ne_zero
    {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L} [DecidableEq (ResidueField A)]
    {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : (N : ResidueField A) ≠ 0)
    {P : (W.map A.subtype).toAffine.Point} (hP : addOrderOf P = N) :
    addOrderOf (reduceHom hΔ P) = N := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_addOrderOf_reduceHom_of_natCast_ne_zero.solution
