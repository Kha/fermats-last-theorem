import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_eq_of_reduceHom_eq_of_nsmul_eq_zero

open WeierstrassCurve IsLocalRing

theorem WeierstrassCurve.eq_of_reduceHom_eq_of_nsmul_eq_zero
    {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L} [DecidableEq (ResidueField A)]
    {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : (N : ResidueField A) ≠ 0)
    {P Q : (W.map A.subtype).toAffine.Point} (hP : N • P = 0) (hQ : N • Q = 0)
    (h : reduceHom hΔ P = reduceHom hΔ Q) : P = Q := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_eq_of_reduceHom_eq_of_nsmul_eq_zero.solution
