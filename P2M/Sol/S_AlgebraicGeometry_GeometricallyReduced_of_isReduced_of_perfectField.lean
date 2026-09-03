import Mathlib
import Theorems.Thm_Algebra_TensorProduct_isReduced_of_perfectField_of_isReduced
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_GeometricallyReduced_of_isReduced_of_perfectField
set_option autoImplicit false
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u v w

namespace F2aux

scoped instance isReduced_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (IsReduced : ObjectProperty Scheme.{u}) where
  of_iso e _ := isReduced_of_isOpenImmersion e.inv

lemma isReduced_pullback_Spec {k : Type u} [Field k] [PerfectField k]
    {R : CommRingCat.{u}} (g : Spec R ⟶ Spec (CommRingCat.of k)) (hred : IsReduced (Spec R))
    (hft : LocallyOfFiniteType g) (K : Type u) [Field K] [Algebra k K] :
    IsReduced (pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  algebraize [φ.hom]
  have hft' : Algebra.FiniteType k R := by
    rw [← RingHom.finiteType_algebraMap]
    exact HasRingHomProperty.Spec_iff.mp hft
  have hred' : _root_.IsReduced R := (affine_isReduced_iff R).mp hred
  have hKR : _root_.IsReduced (K ⊗[k] R) :=
    Algebra.TensorProduct.isReduced_of_perfectField_of_isReduced k R K
  have hRK : _root_.IsReduced (R ⊗[k] K) :=
    isReduced_of_injective (Algebra.TensorProduct.comm k R K).toRingHom
      (Algebra.TensorProduct.comm k R K).injective
  have : IsReduced (Spec (CommRingCat.of (R ⊗[k] K))) := (affine_isReduced_iff _).mpr hRK
  let e : pullback (Spec.map φ) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≅
      Spec (CommRingCat.of (R ⊗[k] K)) :=
    pullbackSpecIso k R K
  exact isReduced_of_isOpenImmersion e.hom

end F2aux
p2m_reactivate "P2MW.S_AlgebraicGeometry_GeometricallyReduced_of_isReduced_of_perfectField.F2aux"

theorem solution {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [IsReduced X] :
    GeometricallyReduced f := by
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms (P := IsReduced)).mpr ?_⟩
  intro K _ _

  apply +allowSynthFailures @IsReduced.of_openCover
    (𝒰 := Scheme.Pullback.openCoverOfLeft X.affineCover f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  intro i
  rw [Scheme.Pullback.openCoverOfLeft_X]

  have hred : IsReduced (X.affineCover.X i) := isReduced_of_isOpenImmersion (X.affineCover.f i)
  have hft : LocallyOfFiniteType (X.affineCover.f i ≫ f) := inferInstance
  exact F2aux.isReduced_pullback_Spec (X.affineCover.f i ≫ f) hred hft K
