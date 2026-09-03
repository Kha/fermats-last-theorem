import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_reduceHom_surjective_of_henselianLocalRing

theorem WeierstrassCurve.reduceHom_surjective_of_henselianLocalRing
    {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L} [HenselianLocalRing A]
    [DecidableEq (IsLocalRing.ResidueField A)]
    {W : WeierstrassCurve A} (hΔ : (W.map (IsLocalRing.residue A)).Δ ≠ 0) :
    Function.Surjective (WeierstrassCurve.reduceHom hΔ) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_reduceHom_surjective_of_henselianLocalRing.solution
