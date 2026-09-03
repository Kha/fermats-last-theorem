import Mathlib
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuli_existsUnique_comp_eq_and_isIso
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_QM_IsCoarseModuli_exists_iso_comp_eq_of_isCoarseModuli

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian
open scoped Quaternion

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ) {B : Type} [CommRing B]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of B))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)), FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (hX : IsCoarseModuli Λ N X πX pt)
    (X' : Scheme.{0}) (πX' : X' ⟶ Spec (CommRingCat.of B))
    (pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)), FakeEllipticCurve Λ N S → SchemeHomOver s πX')
    (hX' : IsCoarseModuli Λ N X' πX' pt') :
    ∃ i : X ≅ X', i.hom ≫ πX' = πX ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (E : FakeEllipticCurve Λ N S),
        (pt' S s E).1 = (pt S s E).1 ≫ i.hom := by
  obtain ⟨⟨g, ⟨hgπ, hgpt⟩, _⟩, hiso⟩ :=
    CerednikDrinfeld.QM.IsCoarseModuli.existsUnique_comp_eq_and_isIso hX hX'
  haveI : IsIso g := hiso g hgπ hgpt
  exact ⟨asIso g, hgπ, hgpt⟩
