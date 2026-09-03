import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_Deformation_wittHomMap_eq_zero_iff_forall_coeff_mem_hopfKer

universe u v w

theorem Deformation.wittHomMap_eq_zero_iff_forall_coeff_mem_hopfKer
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] {n : ℕ}
    {A : Type v} [CommRing A] [Bialgebra R A] {B : Type w} [CommRing B] [Bialgebra R B]
    (π : A →ₐc[R] B) (x : Deformation.wittHom R p n A) :
    Deformation.wittHomMap p n π x = 0 ↔
      ∀ i, (x : TruncatedWittVector p n A).coeff i ∈ HopfAlgebra.hopfKer π := by p2m_exact_reverting @_root_.P2MW.S_Deformation_wittHomMap_eq_zero_iff_forall_coeff_mem_hopfKer.solution
