import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_Deformation_DieudonneModule_exists_coe_eq_nsmulAlgHom_and_map_eq_nsmul

universe u v

theorem Deformation.DieudonneModule.exists_coe_eq_nsmulAlgHom_and_map_eq_nsmul
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (A : Type v) [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A] (n : ℕ) :
    ∃ φ : A →ₐc[R] A, (φ : A →ₐ[R] A) = PDivisibleGroup.Hopf.nsmulAlgHom R A n ∧
      ∀ z : Deformation.DieudonneModule R p A,
        Deformation.DieudonneModule.map R p φ z = n • z := by p2m_exact_reverting @_root_.P2MW.S_Deformation_DieudonneModule_exists_coe_eq_nsmulAlgHom_and_map_eq_nsmul.solution
