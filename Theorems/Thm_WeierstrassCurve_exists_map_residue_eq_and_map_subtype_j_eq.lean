import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_map_residue_eq_and_map_subtype_j_eq

theorem WeierstrassCurve.exists_map_residue_eq_and_map_subtype_j_eq {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) (W : WeierstrassCurve (IsLocalRing.ResidueField A)) [W.IsElliptic] (β : A) (hres : IsLocalRing.residue A β = W.j) : ∃ (E : WeierstrassCurve A) (_ : (E.map A.subtype).IsElliptic), E.map (IsLocalRing.residue A) = W ∧ (E.map A.subtype).j = (β : L) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_map_residue_eq_and_map_subtype_j_eq.solution
