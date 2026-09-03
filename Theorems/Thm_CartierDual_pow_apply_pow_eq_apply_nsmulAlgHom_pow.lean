import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_CartierDual_pow_apply_pow_eq_apply_nsmulAlgHom_pow

set_option autoImplicit false

universe u v

theorem CartierDual.pow_apply_pow_eq_apply_nsmulAlgHom_pow
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    {A : Type v} [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Free R A]
    [Coalgebra.IsCocomm R A] (φ : CartierDual R A) (a : A) :
    (φ ^ p) (a ^ p) = φ (PDivisibleGroup.Hopf.nsmulAlgHom R A p a) ^ p := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_pow_apply_pow_eq_apply_nsmulAlgHom_pow.solution
