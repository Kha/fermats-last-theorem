import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import P2M.Util
import P2M.Sol.S_Deformation_DieudonneModule_exists_ker_verschiebung_addEquiv_primitives_apply_of_eq_and_apply_map

set_option autoImplicit false

theorem Deformation.DieudonneModule.exists_ker_verschiebung_addEquiv_primitives_apply_of_eq_and_apply_map
    (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type*) [CommRing A] [HopfAlgebra k A] :
    ∃ e : (Deformation.DieudonneModule.verschiebung k p A).ker ≃+ ↥(primitives k A),
      (∀ (x : Deformation.wittHom k p 1 A)
          (hx : Deformation.DieudonneModule.of k p A 1 x ∈ (Deformation.DieudonneModule.verschiebung k p A).ker),
        (e ⟨Deformation.DieudonneModule.of k p A 1 x, hx⟩ : A) = (x : TruncatedWittVector p 1 A).coeff 0) ∧
      ∀ (ψ : A →ₐc[k] A) (z : (Deformation.DieudonneModule.verschiebung k p A).ker)
        (hz : Deformation.DieudonneModule.map k p ψ z ∈ (Deformation.DieudonneModule.verschiebung k p A).ker),
        (e ⟨Deformation.DieudonneModule.map k p ψ z, hz⟩ : A) = ψ (e z : A) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_DieudonneModule_exists_ker_verschiebung_addEquiv_primitives_apply_of_eq_and_apply_map.solution
