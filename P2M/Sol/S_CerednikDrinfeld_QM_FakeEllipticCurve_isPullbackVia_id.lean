import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isPullbackVia_id

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S) :
    FakeEllipticCurve.IsPullbackVia (RingHom.id S) E E (𝟙 E.A) := by
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 _ := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
  have hg : IsPullback (𝟙 E.A) E.f E.f (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by
    rw [hid]; exact IsPullback.of_id_fst
  refine ⟨hg, ?_, ?_, ?_⟩
  · intro T t' P Q
    have key : ∀ (t₂ : T ⟶ Spec (CommRingCat.of S)) (ht : t' = t₂)
        (P' Q' : SchemeHomOver t₂ E.f), P'.1 = P.1 → Q'.1 = Q.1 →
        (E.L.mul t₂ P' Q').1 = (E.L.mul t' P Q).1 := by
      rintro t₂ rfl P' Q' hP hQ
      have hP' : P' = P := Subtype.ext hP
      have hQ' : Q' = Q := Subtype.ext hQ
      subst hP' hQ'
      rfl
    rw [Category.comp_id]
    exact (key _ (by rw [hid, Category.comp_id]) _ _ (Category.comp_id _) (Category.comp_id _)).symm
  · intro x
    rw [Category.comp_id, Category.id_comp]
  · intro T t' P hP
    obtain ⟨P₀, h⟩ := hP
    exact ⟨P₀, by rw [Category.comp_id]; exact h⟩
