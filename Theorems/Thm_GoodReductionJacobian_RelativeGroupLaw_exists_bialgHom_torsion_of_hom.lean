import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_bialgHom_torsion_of_hom
attribute [-simp] GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_bialgHom_torsion_of_hom
    {R : Type u} [CommRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (u : SchemeHomOver g f)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LB.mul t x y) u =
        L.mul t (NeronModelInfra.schemeHomOverComp x u) (NeronModelInfra.schemeHomOverComp y u))
    (n : ℕ)
    (HB : Type u) [CommRing HB] [HopfAlgebra R HB] (HJ : Type u) [CommRing HJ] [HopfAlgebra R HJ]
    (eB : ∀ (T : Type u) [CommRing T] [Algebra R T],
        WithConv (HB →ₐ[R] T) ≃
          LB.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n)
    (eB_mul : ∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (HB →ₐ[R] T)),
        ((eB T (φ * ψ)).val : SchemeHomOver _ g) =
          LB.mul _ (eB T φ).val (eB T ψ).val)
    (eB_nat : ∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
        (a : T →ₐ[R] T') (φ : WithConv (HB →ₐ[R] T)),
        ((eB T' (.toConv (a.comp φ.ofConv))).val : SchemeHomOver _ g).1 =
          Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (eB T φ).val.1)
    (eJ : ∀ (T : Type u) [CommRing T] [Algebra R T],
        WithConv (HJ →ₐ[R] T) ≃
          L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n)
    (eJ_mul : ∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (HJ →ₐ[R] T)),
        ((eJ T (φ * ψ)).val : SchemeHomOver _ f) =
          L.mul _ (eJ T φ).val (eJ T ψ).val)
    (eJ_nat : ∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
        (a : T →ₐ[R] T') (φ : WithConv (HJ →ₐ[R] T)),
        ((eJ T' (.toConv (a.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
          Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (eJ T φ).val.1) :
    ∃ φ : HJ →ₐc[R] HB, ∀ (T : Type u) [CommRing T] [Algebra R T] (x : WithConv (HB →ₐ[R] T)),
      ((eJ T (.toConv (x.ofConv.comp (φ : HJ →ₐ[R] HB)))).val : SchemeHomOver _ f) =
        NeronModelInfra.schemeHomOverComp ((eB T x).val : SchemeHomOver _ g) u := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_bialgHom_torsion_of_hom.solution
