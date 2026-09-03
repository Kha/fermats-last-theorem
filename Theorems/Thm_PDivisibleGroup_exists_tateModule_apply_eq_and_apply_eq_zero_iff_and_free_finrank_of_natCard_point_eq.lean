import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_PDivisibleGroup_Points
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_tateModule_apply_eq_and_apply_eq_zero_iff_and_free_finrank_of_natCard_point_eq

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.exists_tateModule_apply_eq_and_apply_eq_zero_iff_and_free_finrank_of_natCard_point_eq
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] {h : ℕ} (H : PDivisibleGroup O p h)
    (L : Type) [CommRing L] [Algebra O L]
    (hcard : ∀ v : ℕ, Finite (H.Point L v) ∧ Nat.card (H.Point L v) = p ^ (v * h)) :
    (∀ (v : ℕ) (x : H.Point L v), ∃ y : TateModule p (H.Points L),
      (y : ℕ → H.Points L) v = H.pointsMkAdd L v (Additive.ofMul x)) ∧
    (∀ (v : ℕ) (y : TateModule p (H.Points L)),
      (y : ℕ → H.Points L) v = 0 ↔ ∃ z : TateModule p (H.Points L), y = ((p : ℤ_[p]) ^ v) • z) ∧
    Module.Free ℤ_[p] (TateModule p (H.Points L)) ∧ Module.finrank ℤ_[p] (TateModule p (H.Points L)) = h := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_tateModule_apply_eq_and_apply_eq_zero_iff_and_free_finrank_of_natCard_point_eq.solution
