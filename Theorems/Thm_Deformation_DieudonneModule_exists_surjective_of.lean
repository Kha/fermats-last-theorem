import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import P2M.Util
import P2M.Sol.S_Deformation_DieudonneModule_exists_surjective_of

universe u v

theorem Deformation.DieudonneModule.exists_surjective_of
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A] :
    ∃ N : ℕ, Function.Surjective (Deformation.DieudonneModule.of k p A N) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_DieudonneModule_exists_surjective_of.solution
