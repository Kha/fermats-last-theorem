import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import P2M.Util
import P2M.Sol.S_Deformation_DieudonneModule_nonempty_ker_verschiebung_addEquiv_primitives

set_option autoImplicit false

theorem Deformation.DieudonneModule.nonempty_ker_verschiebung_addEquiv_primitives
    (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type*) [CommRing A] [HopfAlgebra k A] :
    Nonempty ((Deformation.DieudonneModule.verschiebung k p A).ker ≃+ ↥(primitives k A)) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_DieudonneModule_nonempty_ker_verschiebung_addEquiv_primitives.solution
