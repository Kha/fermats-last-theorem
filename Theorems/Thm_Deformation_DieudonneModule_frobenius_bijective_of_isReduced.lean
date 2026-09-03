import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import P2M.Util
import P2M.Sol.S_Deformation_DieudonneModule_frobenius_bijective_of_isReduced

universe v

theorem Deformation.DieudonneModule.frobenius_bijective_of_isReduced
    (p : ℕ) [Fact p.Prime] (B : Type v) [CommRing B] [Bialgebra (ZMod p) B] [Module.Finite (ZMod p) B]
    (hB : IsReduced B) :
    Function.Bijective (Deformation.DieudonneModule.frobenius (ZMod p) p B) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_DieudonneModule_frobenius_bijective_of_isReduced.solution
