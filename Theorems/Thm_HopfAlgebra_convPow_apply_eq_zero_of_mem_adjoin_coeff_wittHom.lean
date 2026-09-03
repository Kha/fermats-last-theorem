import Definitions.Def_Dieudonne_WittVectorHom
import P2M.Util
import P2M.Sol.S_HopfAlgebra_convPow_apply_eq_zero_of_mem_adjoin_coeff_wittHom

set_option autoImplicit false

universe u v

theorem HopfAlgebra.convPow_apply_eq_zero_of_mem_adjoin_coeff_wittHom
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ) [NeZero n]
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
    (β : WithConv (A →ₗ[k] k)) (hβ : β.ofConv 1 = 0) (s : A)
    (hs : s ∈ Algebra.adjoin k {a : A | ∃ x : Deformation.wittHom k p n A, ∃ j : Fin n,
          (x : TruncatedWittVector p n A).coeff j = a}) :
    (β ^ p ^ n).ofConv s = 0 := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_convPow_apply_eq_zero_of_mem_adjoin_coeff_wittHom.solution
