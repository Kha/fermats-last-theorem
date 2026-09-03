import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_Resolution_exists_twoAffineLineCover_subscheme_of_chartTable

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem MvPolynomial.CrossingQuotient.Resolution.exists_twoAffineLineCover_subscheme_of_chartTable
    {W : Type u} [CommRing W] (t : W) (e : ℕ)
    (F : Fin (e + 1) → (MvPolynomial.CrossingQuotient.Resolution t e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (MvPolynomial.CrossingQuotient.Resolution.ι t e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {MvPolynomial.CrossingQuotient.V t} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {MvPolynomial.CrossingQuotient.U t} else ⊤)))
    (d : ℕ) (hd0 : 0 < d) (hde : d < e)
    (k₀ : Type u) [Field k₀] [Algebra W k₀] (hq : Function.Surjective (algebraMap W k₀))
    (hker : RingHom.ker (algebraMap W k₀) = Ideal.span {t}) :
    ∃ (z : (F ⟨d, by omega⟩).subscheme ⟶ Spec (CommRingCat.of k₀))
      (i₀ i₁ : Spec (CommRingCat.of (Polynomial k₀)) ⟶ (F ⟨d, by omega⟩).subscheme),
      IsOpenImmersion i₀ ∧ IsOpenImmersion i₁ ∧
      z ≫ Spec.map (CommRingCat.ofHom (algebraMap W k₀)) = (F ⟨d, by omega⟩).subschemeι ≫ MvPolynomial.CrossingQuotient.Resolution.toSpec t e ∧
      i₀ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀))) ∧
      i₁ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀))) ∧
      Set.range i₀.base ∪ Set.range i₁.base = Set.univ ∧
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k₀) (Localization.Away (Polynomial.X : Polynomial k₀)))) ≫ i₀ =
        Spec.map (CommRingCat.ofHom (Polynomial.aeval (R := k₀)
          (IsLocalization.Away.invSelf (S := Localization.Away (Polynomial.X : Polynomial k₀)) (Polynomial.X : Polynomial k₀))).toRingHom) ≫ i₁ ∧
      Set.range i₀.base ∩ Set.range i₁.base ⊆
        Set.range (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k₀) (Localization.Away (Polynomial.X : Polynomial k₀)))) ≫ i₀).base ∧
      Set.range (i₀ ≫ (F ⟨d, by omega⟩).subschemeι).base ⊆ Set.range (MvPolynomial.CrossingQuotient.Resolution.ι t e ⟨d - 1, by omega⟩).base ∧
      Set.range (i₁ ≫ (F ⟨d, by omega⟩).subschemeι).base ⊆ Set.range (MvPolynomial.CrossingQuotient.Resolution.ι t e ⟨d, hde⟩).base := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_Resolution_exists_twoAffineLineCover_subscheme_of_chartTable.solution
