import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_toConv_id_pow_eq_one_baseChange

universe u v w

theorem HopfAlgebra.toConv_id_pow_eq_one_baseChange
    {R : Type u} [CommRing R] (R' : Type w) [CommRing R'] [Algebra R R']
    {H : Type v} [CommRing H] [HopfAlgebra R H] (m : ℕ)
    (h : (WithConv.toConv (AlgHom.id R H)) ^ m = 1) :
    (WithConv.toConv (AlgHom.id R' (TensorProduct R R' H))) ^ m = 1 := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_toConv_id_pow_eq_one_baseChange.solution
