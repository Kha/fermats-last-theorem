import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_bialgHom_of_schemeHomOver_of_forall_mul

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_bialgHom_of_schemeHomOver_of_forall_mul
    {R : Type u} [CommRing R]
    {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R g) [IsAffineHom g]
    {A' : Scheme.{u}} {g' : A' ⟶ Spec (CommRingCat.of R)} (L' : RelativeGroupLaw R g') [IsAffineHom g']
    (u : SchemeHomOver g' g)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g'),
      (⟨(L'.mul t x y).1 ≫ u.1, by rw [Category.assoc, u.2, (L'.mul t x y).2]⟩ : SchemeHomOver t g) =
        L.mul t ⟨x.1 ≫ u.1, by rw [Category.assoc, u.2, x.2]⟩ ⟨y.1 ≫ u.1, by rw [Category.assoc, u.2, y.2]⟩)
    (H : Type u) [CommRing H] [HopfAlgebra R H] (H' : Type u) [CommRing H'] [HopfAlgebra R H'] :
    letI : Algebra R Γ(A, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom.toAlgebra
    letI : Algebra R Γ(A', ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g'.appTop).hom.toAlgebra
    haveI : IsAffine A := isAffine_of_isAffineHom g
    haveI : IsAffine A' := isAffine_of_isAffineHom g'
    ∀ (iso : H ≃ₐ[R] Γ(A, ⊤)) (iso' : H' ≃ₐ[R] Γ(A', ⊤))
      (e : ∀ (T : Type u) [CommRing T] [Algebra R T],
        WithConv (H →ₐ[R] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) g)
      (e' : ∀ (T : Type u) [CommRing T] [Algebra R T],
        WithConv (H' →ₐ[R] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) g'),
      (∀ (T : Type u) [CommRing T] [Algebra R T] (φ : WithConv (H →ₐ[R] T)),
        (e T φ).1 = Spec.map (CommRingCat.ofHom ((φ.ofConv.comp (iso.symm : Γ(A, ⊤) →ₐ[R] H)).toRingHom)) ≫ A.isoSpec.inv) →
      (∀ (T : Type u) [CommRing T] [Algebra R T] (φ : WithConv (H' →ₐ[R] T)),
        (e' T φ).1 = Spec.map (CommRingCat.ofHom ((φ.ofConv.comp (iso'.symm : Γ(A', ⊤) →ₐ[R] H')).toRingHom)) ≫ A'.isoSpec.inv) →
      (∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)), e T (φ * ψ) = L.mul _ (e T φ) (e T ψ)) →
      (∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H' →ₐ[R] T)), e' T (φ * ψ) = L'.mul _ (e' T φ) (e' T ψ)) →
      ∃ ψ : H →ₐc[R] H',
        (∀ h : H, iso' (ψ h) = u.1.appTop.hom (iso h)) ∧
        (∀ (T : Type u) [CommRing T] [Algebra R T] (φ' : WithConv (H' →ₐ[R] T)),
          (e T (.toConv (φ'.ofConv.comp (ψ : H →ₐ[R] H')))).1 = (e' T φ').1 ≫ u.1) ∧
        (IsClosedImmersion u.1 → Function.Surjective ψ) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_bialgHom_of_schemeHomOver_of_forall_mul.solution
