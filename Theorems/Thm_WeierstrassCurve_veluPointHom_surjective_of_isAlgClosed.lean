import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_veluPointHom_surjective_of_isAlgClosed

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
theorem WeierstrassCurve.veluPointHom_surjective_of_isAlgClosed
    {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓK : (ℓ : K) ≠ 0)
    (Q : W.toAffine.Point) (hQord : addOrderOf Q = ℓ) :
    let S := W.oddOrderSummingSet Q (ℓ / 2)
    ∀ φ : W.toAffine.Point →+ (W.veluQuotient S).toAffine.Point,
      (∀ (x y : K) (h : W.toAffine.Nonsingular x y),
        (.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
          ∃ h', φ (.some x y h) = .some (W.veluX S x) (W.veluY S x y) h') →
      Function.Surjective φ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_veluPointHom_surjective_of_isAlgClosed.solution
