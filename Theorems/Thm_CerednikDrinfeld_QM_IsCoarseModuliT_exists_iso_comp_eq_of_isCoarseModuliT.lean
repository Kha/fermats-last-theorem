import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_IsCoarseModuliT_exists_iso_comp_eq_of_isCoarseModuliT

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian
open scoped Quaternion

theorem CerednikDrinfeld.QM.IsCoarseModuliT.exists_iso_comp_eq_of_isCoarseModuliT
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ) {B : Type} [CommRing B]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of B))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)), FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πX)
    (hX : IsCoarseModuliT Λ N ℓ X πX pt)
    (X' : Scheme.{0}) (πX' : X' ⟶ Spec (CommRingCat.of B))
    (pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)), FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πX')
    (hX' : IsCoarseModuliT Λ N ℓ X' πX' pt') :
    ∃ i : X ≅ X', i.hom ≫ πX' = πX ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (E : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
        (pt' S s E).1 = (pt S s E).1 ≫ i.hom := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_IsCoarseModuliT_exists_iso_comp_eq_of_isCoarseModuliT.solution
