import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_Hopf_nsmulAlgHom_eq_sum_pow_apply_smul_pow

set_option autoImplicit false

universe u v w

theorem PDivisibleGroup.Hopf.nsmulAlgHom_eq_sum_pow_apply_smul_pow
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    {A : Type v} [CommRing A] [Bialgebra R A] [Coalgebra.IsCocomm R A]
    {ι : Type w} [Fintype ι] (b : Module.Basis ι R A) (a : A) :
    PDivisibleGroup.Hopf.nsmulAlgHom R A p a =
      ∑ i, (CartierDual.ofDual R A (b.coord i) ^ p) a • b i ^ p := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_Hopf_nsmulAlgHom_eq_sum_pow_apply_smul_pow.solution
