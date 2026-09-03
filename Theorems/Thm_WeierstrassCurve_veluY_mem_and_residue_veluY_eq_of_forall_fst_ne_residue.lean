import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_veluY_mem_and_residue_veluY_eq_of_forall_fst_ne_residue

theorem WeierstrassCurve.veluY_mem_and_residue_veluY_eq_of_forall_fst_ne_residue
    {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
    [DecidableEq (IsLocalRing.ResidueField A)]
    {E : WeierstrassCurve A} (hΔ : (E.map (IsLocalRing.residue A)).Δ ≠ 0) {n : ℕ}
    (hm : ((2 * n + 1 : ℕ) : IsLocalRing.ResidueField A) ≠ 0)
    (Q : (E.map A.subtype).toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1)
    (hQ' : addOrderOf (WeierstrassCurve.reduceHom hΔ Q) = 2 * n + 1)
    {x y : L} (hx : x ∈ A) (hy : y ∈ A)
    (hx' : ∀ P ∈ (E.map (IsLocalRing.residue A)).oddOrderSummingSet
      (WeierstrassCurve.reduceHom hΔ Q) n, P.1 ≠ IsLocalRing.residue A ⟨x, hx⟩) :
    ∃ hmem : (E.map A.subtype).veluY ((E.map A.subtype).oddOrderSummingSet Q n) x y ∈ A,
      IsLocalRing.residue A ⟨_, hmem⟩ =
        (E.map (IsLocalRing.residue A)).veluY
          ((E.map (IsLocalRing.residue A)).oddOrderSummingSet (WeierstrassCurve.reduceHom hΔ Q) n)
          (IsLocalRing.residue A ⟨x, hx⟩) (IsLocalRing.residue A ⟨y, hy⟩) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_veluY_mem_and_residue_veluY_eq_of_forall_fst_ne_residue.solution
