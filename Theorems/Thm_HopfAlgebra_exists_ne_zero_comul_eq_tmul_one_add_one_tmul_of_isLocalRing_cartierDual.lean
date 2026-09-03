import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_ne_zero_comul_eq_tmul_one_add_one_tmul_of_isLocalRing_cartierDual

universe u v

theorem HopfAlgebra.exists_ne_zero_comul_eq_tmul_one_add_one_tmul_of_isLocalRing_cartierDual
    (k : Type u) [Field k] (A : Type v) [CommRing A] [Bialgebra k A] [Coalgebra.IsCocomm k A]
    [Module.Finite k A] (hA : IsLocalRing (CartierDual k A)) (hrank : Module.finrank k A ≠ 1) :
    ∃ a : A, a ≠ 0 ∧ Coalgebra.comul (R := k) a = a ⊗ₜ[k] 1 + 1 ⊗ₜ[k] a := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_ne_zero_comul_eq_tmul_one_add_one_tmul_of_isLocalRing_cartierDual.solution
