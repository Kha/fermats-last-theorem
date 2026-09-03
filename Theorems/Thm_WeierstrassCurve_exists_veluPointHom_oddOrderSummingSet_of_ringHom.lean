import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_ringHom
open WeierstrassCurve
theorem WeierstrassCurve.exists_veluPointHom_oddOrderSummingSet_of_ringHom
    {F L : Type*} [Field F] [DecidableEq F] [Field L] [DecidableEq L] (f : F →+* L)
    (W : WeierstrassCurve F) [W.IsElliptic]
    {p : ℕ} (Q : W.toAffine.Point) (hQord : addOrderOf Q = p)
    (hL : ∀ (W' : WeierstrassCurve L) [W'.IsElliptic] (Q' : W'.toAffine.Point), addOrderOf Q' = p →
      let S' := W'.oddOrderSummingSet Q' (p / 2)
      ∃ φ' : W'.toAffine.Point →+ (W'.veluQuotient S').toAffine.Point,
        φ'.ker = AddSubgroup.zmultiples Q' ∧
        (∀ (x y : L) (h : W'.toAffine.Nonsingular x y),
          (.some x y h : W'.toAffine.Point) ∉ AddSubgroup.zmultiples Q' →
            ∃ h', φ' (.some x y h) = .some (W'.veluX S' x) (W'.veluY S' x y) h')) :
    let S := W.oddOrderSummingSet Q (p / 2)
    ∃ φ : W.toAffine.Point →+ (W.veluQuotient S).toAffine.Point,
      φ.ker = AddSubgroup.zmultiples Q ∧
      (∀ (x y : F) (h : W.toAffine.Nonsingular x y),
        (.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
          ∃ h', φ (.some x y h) = .some (W.veluX S x) (W.veluY S x y) h') := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_ringHom.solution
