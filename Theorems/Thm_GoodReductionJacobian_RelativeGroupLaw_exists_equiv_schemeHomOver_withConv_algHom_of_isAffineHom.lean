import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_equiv_schemeHomOver_withConv_algHom_of_isAffineHom

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_equiv_schemeHomOver_withConv_algHom_of_isAffineHom
    {X : Scheme.{0}} {gX : X ⟶ Spec (CommRingCat.of ℤ)} (LX : RelativeGroupLaw ℤ gX) [IsAffineHom gX]
    (H : Type) [CommRing H] [HopfAlgebra ℤ H]
    (ePts : ∀ (T : Type) [CommRing T] [Algebra ℤ T],
      WithConv (H →ₐ[ℤ] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ T))) gX)
    (hePts_mul : ∀ (T : Type) [CommRing T] [Algebra ℤ T] (φ ψ : WithConv (H →ₐ[ℤ] T)),
      ePts T (φ * ψ) = LX.mul _ (ePts T φ) (ePts T ψ))
    (hePts_nat : ∀ (T T' : Type) [CommRing T] [Algebra ℤ T] [CommRing T'] [Algebra ℤ T']
        (σ : T →ₐ[ℤ] T') (φ : WithConv (H →ₐ[ℤ] T)),
      (ePts T' (.toConv (σ.comp φ.ofConv))).1 = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (ePts T φ).1) :
    ∃ eU : ∀ (U : Scheme.{0}) (u : U ⟶ Spec (CommRingCat.of ℤ)), SchemeHomOver u gX ≃ WithConv (H →ₐ[ℤ] Γ(U, ⊤)),

      (∀ (U : Scheme.{0}) (u : U ⟶ Spec (CommRingCat.of ℤ)) (y : SchemeHomOver u gX),
        y.1 = U.toSpecΓ ≫ (ePts Γ(U, ⊤) (eU U u y)).1) ∧

      (∀ (U : Scheme.{0}) (u : U ⟶ Spec (CommRingCat.of ℤ)) (y y' : SchemeHomOver u gX),
        eU U u (LX.mul u y y') = eU U u y * eU U u y') ∧

      (∀ (U V : Scheme.{0}) (u : U ⟶ Spec (CommRingCat.of ℤ)) (v : V ⟶ Spec (CommRingCat.of ℤ)) (ψ : V ⟶ U)
          (hψ : ψ ≫ u = v) (y : SchemeHomOver u gX) (h : H),
        (eU V v (GoodReductionJacobian.schemeHomOverComp ψ hψ y)).ofConv h = (Scheme.Γ.map ψ.op) ((eU U u y).ofConv h)) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_equiv_schemeHomOver_withConv_algHom_of_isAffineHom.solution
