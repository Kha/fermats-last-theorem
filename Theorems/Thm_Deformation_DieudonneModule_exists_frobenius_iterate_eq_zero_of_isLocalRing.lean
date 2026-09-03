import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import P2M.Util
import P2M.Sol.S_Deformation_DieudonneModule_exists_frobenius_iterate_eq_zero_of_isLocalRing

universe v

theorem Deformation.DieudonneModule.exists_frobenius_iterate_eq_zero_of_isLocalRing
    (p : ℕ) [Fact p.Prime] (B : Type v) [CommRing B] [Bialgebra (ZMod p) B] [Module.Finite (ZMod p) B]
    (hB : IsLocalRing B) :
    ∃ n : ℕ, ∀ z : Deformation.DieudonneModule (ZMod p) p B,
      (Deformation.DieudonneModule.frobenius (ZMod p) p B)^[n] z = 0 := by p2m_exact_reverting @_root_.P2MW.S_Deformation_DieudonneModule_exists_frobenius_iterate_eq_zero_of_isLocalRing.solution
