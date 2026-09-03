import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_IsCoarseModuliT_existsUnique_hom_comp_eq_specMap_ringEquiv

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.IsCoarseModuliT.existsUnique_hom_comp_eq_specMap_ringEquiv
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ) {K : Type} [CommRing K]
    (𝒴 : Scheme.{0}) (g : 𝒴 ⟶ Spec (CommRingCat.of K))
    (ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of K)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s g)
    (hco : IsCoarseModuliT Λ N ℓ 𝒴 g ptT) (τ : K ≃+* K) :
    ∃! h : 𝒴 ⟶ 𝒴, h ≫ g = g ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K)) ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of K))
        (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
        (ptT S (s ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K))) u).1 = (ptT S s u).1 ≫ h := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_IsCoarseModuliT_existsUnique_hom_comp_eq_specMap_ringEquiv.solution
