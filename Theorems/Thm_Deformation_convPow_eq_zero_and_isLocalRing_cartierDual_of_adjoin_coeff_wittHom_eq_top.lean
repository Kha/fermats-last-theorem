import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_Deformation_convPow_eq_zero_and_isLocalRing_cartierDual_of_adjoin_coeff_wittHom_eq_top

universe u v

theorem Deformation.convPow_eq_zero_and_isLocalRing_cartierDual_of_adjoin_coeff_wittHom_eq_top
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ)
    (A : Type v) [CommRing A] [Bialgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]
    (hgen : Algebra.adjoin k {a : A | ∃ (x : Deformation.wittHom k p n A) (i : Fin n),
      (x : TruncatedWittVector p n A).coeff i = a} = ⊤) :
    (∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ n = 0) ∧
      IsLocalRing (CartierDual k A) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_convPow_eq_zero_and_isLocalRing_cartierDual_of_adjoin_coeff_wittHom_eq_top.solution
