import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import P2M.Util
import P2M.Sol.S_Deformation_mem_wittHom_succ_iff_comul_eq_of_forall_coeff_eq_zero

universe u v

theorem Deformation.mem_wittHom_succ_iff_comul_eq_of_forall_coeff_eq_zero
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] {n : ℕ}
    {A : Type v} [CommRing A] [Bialgebra R A]
    (x : TruncatedWittVector p (n + 1) A)
    (hx : ∀ i : Fin (n + 1), i ≠ Fin.last n → x.coeff i = 0) :
    x ∈ Deformation.wittHom R p (n + 1) A ↔
      Coalgebra.comul (R := R) (x.coeff (Fin.last n)) =
        x.coeff (Fin.last n) ⊗ₜ[R] (1 : A) + (1 : A) ⊗ₜ[R] x.coeff (Fin.last n) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_mem_wittHom_succ_iff_comul_eq_of_forall_coeff_eq_zero.solution
