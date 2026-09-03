import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
namespace P2MW.S_MvPolynomial_CrossingQuotient_Resolution_locallyOfFiniteType_and_quasiCompact_toCrossing

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

open CategoryTheory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient in
theorem solution
    {W : Type u} [CommRing W] (t : W) (e : ℕ) :
    LocallyOfFiniteType (Resolution.toCrossing t e) ∧ QuasiCompact (Resolution.toCrossing t e) := by
  constructor
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType) (Resolution.openCover t e)]
    intro i
    have hι := Resolution.ι_toCrossing t e (i : Fin e)
    change LocallyOfFiniteType (Resolution.ι t e (i : Fin e) ≫ Resolution.toCrossing t e)
    rw [hι, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    change RingHom.FiniteType (resolutionChart t e i).toRingHom
    refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap W (CrossingQuotient W (t ^ e))) ?_
    have hc : (resolutionChart t e i).toRingHom.comp (algebraMap W (CrossingQuotient W (t ^ e))) =
        algebraMap W (CrossingQuotient W t) := RingHom.ext fun w => (resolutionChart t e i).commutes w
    rw [hc, RingHom.finiteType_algebraMap]
    exact Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ W _) (Ideal.Quotient.mkₐ_surjective W _)
  · haveI hc : CompactSpace (chartScheme t) := by
      have h := (isAffineOpen_top (chartScheme t)).isCompact
      exact isCompact_univ_iff.mp (by simpa using h)
    haveI : CompactSpace (Resolution t e) := by
      constructor
      have h : (Set.univ : Set (Resolution t e)) = ⋃ i : Fin e, Set.range (Resolution.ι t e i).base := by
        ext x
        simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
        obtain ⟨i, y, rfl⟩ := Resolution.exists_ι_apply_eq t e x
        exact ⟨i, y, rfl⟩
      rw [h]
      exact isCompact_iUnion fun i => isCompact_range (Resolution.ι t e i).continuous
    exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr ‹CompactSpace (Resolution t e)›
