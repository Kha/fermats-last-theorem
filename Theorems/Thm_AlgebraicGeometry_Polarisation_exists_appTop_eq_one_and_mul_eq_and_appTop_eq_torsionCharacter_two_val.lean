import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_TorsionCharacter
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_exists_appTop_eq_one_and_mul_eq_and_appTop_eq_torsionCharacter_two_val

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard AlgebraicGeometry.DescentCharacter

theorem AlgebraicGeometry.Polarisation.exists_appTop_eq_one_and_mul_eq_and_appTop_eq_torsionCharacter_two_val
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (hker : IsFinite (L.schemeKerStr 2) ∧ Flat (L.schemeKerStr 2) ∧ LocallyOfFinitePresentation (L.schemeKerStr 2))
    (h2fl : IsAffineHom (L.schemeNsmul 2) ∧ Flat (L.schemeNsmul 2) ∧ Surjective (L.schemeNsmul 2))
    (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (χ : L.TorsionCharacter 2 ι)
    {P P₃ : Scheme} (p₁ p₂ : P ⟶ pullback f ι)
    (hp : p₁ ≫ (L.baseChange ι).schemeNsmul 2 = p₂ ≫ (L.baseChange ι).schemeNsmul 2)
    (δ : pullback f ι ⟶ P) (hδ₁ : δ ≫ p₁ = 𝟙 _) (hδ₂ : δ ≫ p₂ = 𝟙 _)
    (a b : P₃ ⟶ P) (hab : a ≫ p₂ = b ≫ p₁) (c : P₃ ⟶ P) (hca : c ≫ p₁ = a ≫ p₁) (hcb : c ≫ p₂ = b ≫ p₂) :
    ∃ u : Γ(P, ⊤), δ.appTop u = 1 ∧ a.appTop u * b.appTop u = c.appTop u ∧
      ∀ (T : Type) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
        (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x)
        (s : pullback f (κ ≫ ι) ⟶ P)
        (hs₁ : s ≫ p₁ = RelPicard.baseChangeSnd f (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι))
        (hs₂ : s ≫ p₂ = (L.baseChange (κ ≫ ι)).translate
              (RelativeGroupLaw.baseChangePointOfBase (κ ≫ ι) (t' := 𝟙 (Spec (CommRingCat.of T)))
                ⟨x.1, by rw [Category.id_comp]; exact x.2⟩) ≫
            RelPicard.baseChangeSnd f (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)),
        s.appTop u =
          (pullback.snd f (κ ≫ ι)).appTop ((Scheme.ΓSpecIso (CommRingCat.of T)).inv ((χ.val T κ x hx : Tˣ) : T)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_exists_appTop_eq_one_and_mul_eq_and_appTop_eq_torsionCharacter_two_val.solution
