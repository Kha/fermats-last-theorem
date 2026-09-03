import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Theorems.Thm_MvPolynomial_CrossingQuotient_isRegularRing_of_irreducible
import P2M.Util
namespace P2MW.S_MvPolynomial_CrossingQuotient_Resolution_isRegularLocalRing_stalk

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

open CategoryTheory AlgebraicGeometry IsLocalRing MvPolynomial MvPolynomial.CrossingQuotient in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) (e : ℕ) (x : Resolution ϖ e) :
    IsRegularLocalRing ((Resolution ϖ e).presheaf.stalk x) := by
  obtain ⟨i, y, rfl⟩ := Resolution.exists_ι_apply_eq ϖ e x
  let eSt : (Resolution ϖ e).presheaf.stalk ((Resolution.ι ϖ e i).base y) ≃+* (chartScheme ϖ).presheaf.stalk y :=
    (asIso ((Resolution.ι ϖ e i).stalkMap y)).commRingCatIsoToRingEquiv
  suffices h : IsRegularLocalRing ((chartScheme ϖ).presheaf.stalk y) from IsRegularLocalRing.of_ringEquiv eSt.symm
  haveI : IsRegularRing (CrossingQuotient R ϖ) := CrossingQuotient.isRegularRing_of_irreducible hϖ
  haveI : IsRegularRing Γ(chartScheme ϖ, ⊤) :=
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient R ϖ))).symm.commRingCatIsoToRingEquiv
  letI : Algebra Γ(chartScheme ϖ, ⊤) ((chartScheme ϖ).presheaf.stalk y) :=
    ((chartScheme ϖ).presheaf.germ ⊤ y trivial).hom.toAlgebra
  haveI := (isAffineOpen_top (chartScheme ϖ)).isLocalization_stalk ⟨y, trivial⟩
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv ((isAffineOpen_top (chartScheme ϖ)).primeIdealOf ⟨y, trivial⟩).asIdeal.primeCompl
      (Localization.AtPrime ((isAffineOpen_top (chartScheme ϖ)).primeIdealOf ⟨y, trivial⟩).asIdeal)
      ((chartScheme ϖ).presheaf.stalk y)).toRingEquiv
