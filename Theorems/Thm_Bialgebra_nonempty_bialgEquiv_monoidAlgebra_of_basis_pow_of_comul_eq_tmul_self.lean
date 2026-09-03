import Mathlib
import P2M.Util
import P2M.Sol.S_Bialgebra_nonempty_bialgEquiv_monoidAlgebra_of_basis_pow_of_comul_eq_tmul_self

open scoped TensorProduct

universe u v

theorem Bialgebra.nonempty_bialgEquiv_monoidAlgebra_of_basis_pow_of_comul_eq_tmul_self
    {R : Type u} [CommRing R] {H : Type v} [CommRing H] [Bialgebra R H]
    (n : ℕ) [NeZero n] (x : H)
    (hΔ : Coalgebra.comul (R := R) x = x ⊗ₜ[R] x) (hε : Coalgebra.counit (R := R) x = 1)
    (hxn : x ^ n = 1)
    (b : Module.Basis (Fin n) R H) (hb : ∀ i : Fin n, b i = x ^ (i : ℕ)) :
    Nonempty (H ≃ₐc[R] MonoidAlgebra R (Multiplicative (ZMod n))) := by p2m_exact_reverting @_root_.P2MW.S_Bialgebra_nonempty_bialgEquiv_monoidAlgebra_of_basis_pow_of_comul_eq_tmul_self.solution
