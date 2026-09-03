import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import P2M.Util
import P2M.Sol.S_Deformation_DieudonneModule_exact_map_hopfKerVal_map

universe u v w

theorem Deformation.DieudonneModule.exact_map_hopfKerVal_map
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
    {A : Type v} [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A]
    {B : Type w} [CommRing B] [HopfAlgebra k B]
    (π : A →ₐc[k] B) :
    Function.Exact (Deformation.DieudonneModule.map k p (HopfAlgebra.hopfKerVal π))
      (Deformation.DieudonneModule.map k p π) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_DieudonneModule_exact_map_hopfKerVal_map.solution
