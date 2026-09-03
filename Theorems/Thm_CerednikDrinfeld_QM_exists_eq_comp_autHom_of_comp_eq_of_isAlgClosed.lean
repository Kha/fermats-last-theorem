import Definitions.Def_CerednikDrinfeld_QMFineModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_exists_eq_comp_autHom_of_comp_eq_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.exists_eq_comp_autHom_of_comp_eq_of_isAlgClosed
    {M X : Scheme.{0}} {G : Type} [Group G] [Finite G] (ρ : G →* Aut M)
    (π : M ⟶ X) (hπ : ∀ g : G, (ρ g).hom ≫ π = π) (haff : IsAffineHom π)
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s})
    (k : Type) [Field k] [IsAlgClosed k] (x x' : Spec (CommRingCat.of k) ⟶ M) (h : x ≫ π = x' ≫ π) :
    ∃ g : G, x' = x ≫ (ρ g).hom := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_exists_eq_comp_autHom_of_comp_eq_of_isAlgClosed.solution
