import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_IsCoarseModuliT_existsUnique_comp_eq_and_isIso

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.IsCoarseModuliT.existsUnique_comp_eq_and_isIso
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} {B : Type} [CommRing B]
    {Y : Scheme.{0}} {πY : Y ⟶ Spec (CommRingCat.of B)}
    {ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πY}
    (hY : IsCoarseModuliT Λ N ℓ Y πY ptT)
    {Y' : Scheme.{0}} {πY' : Y' ⟶ Spec (CommRingCat.of B)}
    {ptT' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πY'}
    (hY' : IsCoarseModuliT Λ N ℓ Y' πY' ptT') :
    (∃! g : Y ⟶ Y', g ≫ πY' = πY ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
        (ptT' S s u).1 = (ptT S s u).1 ≫ g) ∧
    ∀ g : Y ⟶ Y', g ≫ πY' = πY →
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
        (ptT' S s u).1 = (ptT S s u).1 ≫ g) → IsIso g := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_IsCoarseModuliT_existsUnique_comp_eq_and_isIso.solution
