import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import P2M.Util
import P2M.Sol.S_Deformation_wittHom_nsmul_eq_zero_of_forall_convPow_eq_one

universe u v

theorem Deformation.wittHom_nsmul_eq_zero_of_forall_convPow_eq_one
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] {n : ℕ}
    {A : Type v} [CommRing A] [Bialgebra R A] (m : ℕ)
    (hA : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (A →ₐ[R] T)), f ^ m = 1)
    (x : Deformation.wittHom R p n A) : m • x = 0 := by p2m_exact_reverting @_root_.P2MW.S_Deformation_wittHom_nsmul_eq_zero_of_forall_convPow_eq_one.solution
