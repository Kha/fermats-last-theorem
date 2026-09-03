import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one

universe u v w

theorem HopfAlgebra.forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one
    {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H] (m : ℕ) :
    (∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ m = 1) ↔
      (WithConv.toConv (AlgHom.id R H)) ^ m = 1 := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one.solution
