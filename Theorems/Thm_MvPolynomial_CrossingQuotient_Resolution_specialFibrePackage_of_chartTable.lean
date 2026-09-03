import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_Resolution_specialFibrePackage_of_chartTable

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

universe u

theorem MvPolynomial.CrossingQuotient.Resolution.specialFibrePackage_of_chartTable
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}) (e : ℕ)
    (F : Fin (e + 1) → (Resolution ϖ e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (Resolution.ι ϖ e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O ϖ))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {V ϖ} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U ϖ} else ⊤))) :
    (∀ k, (F k).IsInvertible) ∧
    (∏ k, F k = Scheme.IdealSheafData.ofIdealTop (Ideal.span
      {(Resolution.toSpec ϖ e).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ)})) ∧
    (∏ k, F k ^ (k : ℕ) = Scheme.IdealSheafData.ofIdealTop (Ideal.span
      {(Resolution.toCrossing ϖ e).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (ϖ ^ e)))).inv.hom (CrossingQuotient.U (ϖ ^ e)))})) ∧
    (∀ (k : Fin (e + 1)) (z : ↥(Resolution ϖ e)), z ∈ (F k).support →
      (Resolution.toSpec ϖ e).base z = IsLocalRing.closedPoint O) ∧
    (∀ (k : ℕ) (hk0 : 0 < k) (hke : k < e) (z : ↥(Resolution ϖ e)), z ∈ (F ⟨k, by omega⟩).support →
      CrossingQuotient.U (ϖ ^ e) ∈ ((Resolution.toCrossing ϖ e).base z).asIdeal ∧
        CrossingQuotient.V (ϖ ^ e) ∈ ((Resolution.toCrossing ϖ e).base z).asIdeal) ∧
    (∀ (k : ℕ) (hke : k < e), ∃ z : ↥(Resolution ϖ e),
      z ∈ (F ⟨k, by omega⟩).support ∧ z ∈ (F ⟨k + 1, by omega⟩).support) ∧
    (∀ (t : Spec (CommRingCat.of O) ⟶ Resolution ϖ e), t ≫ Resolution.toSpec ϖ e = 𝟙 _ →
      ∀ (dd : ℕ) (hd0 : 0 < dd) (hde : dd < e), t.base (IsLocalRing.closedPoint O) ∈ (F ⟨dd, by omega⟩).support →
      (∀ k : Fin (e + 1), (k : ℕ) ≠ dd → t.base (IsLocalRing.closedPoint O) ∉ (F k).support) →
      IsClosedImmersion t ∧ (t.ker).IsInvertible ∧
        ∃ rr : CrossingQuotient O (ϖ ^ e), t.ker * ∏ k, F k ^ (min (k : ℕ) dd) =
          Scheme.IdealSheafData.ofIdealTop (Ideal.span {(Resolution.toCrossing ϖ e).appTop.hom
            ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (ϖ ^ e)))).inv.hom rr)})) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_Resolution_specialFibrePackage_of_chartTable.solution
