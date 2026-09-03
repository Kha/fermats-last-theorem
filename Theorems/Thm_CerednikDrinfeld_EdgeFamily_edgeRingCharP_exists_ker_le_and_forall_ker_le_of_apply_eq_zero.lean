import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_EdgeFamily_edgeRingCharP_exists_ker_le_and_forall_ker_le_of_apply_eq_zero

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.EdgeFamily.edgeRingCharP.exists_ker_le_and_forall_ker_le_of_apply_eq_zero
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    (κ : Type) [Field κ] (f : EdgeFamily.edgeRingCharP p k →+* κ) :
    ∃ (L : Type) (_ : Field L) (h : EdgeFamily.edgeRingCharP p k →+* L),
      RingHom.ker h ≤ RingHom.ker f ∧
      ∀ (κ₀ : Type) [Field κ₀] (f₀ : EdgeFamily.edgeRingCharP p k →+* κ₀),
        f₀ (EdgeFamily.edgeRingCharP.ξ p k) = 0 → f₀ (EdgeFamily.edgeRingCharP.η p k) = 0 →
        RingHom.ker h ≤ RingHom.ker f₀ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_EdgeFamily_edgeRingCharP_exists_ker_le_and_forall_ker_le_of_apply_eq_zero.solution
