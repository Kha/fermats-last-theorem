import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_Resolution_isClosedImmersion_and_exists_eq_specMap_lift_comp_iota_of_comp_toSpec_eq_id

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

universe u

theorem MvPolynomial.CrossingQuotient.Resolution.isClosedImmersion_and_exists_eq_specMap_lift_comp_iota_of_comp_toSpec_eq_id
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (e : ℕ)
    (F : Fin (e + 1) → (Resolution ϖ e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (ι ϖ e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O ϖ))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {V ϖ} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U ϖ} else ⊤)))
    (t : Spec (CommRingCat.of O) ⟶ Resolution ϖ e) (ht : t ≫ Resolution.toSpec ϖ e = 𝟙 _)
    (d : ℕ) (hd0 : 0 < d) (hde : d < e)
    (hmem : t.base (IsLocalRing.closedPoint O) ∈ (F ⟨d, by omega⟩).support)
    (hnot : ∀ k : Fin (e + 1), (k : ℕ) ≠ d → t.base (IsLocalRing.closedPoint O) ∉ (F k).support) :
    IsClosedImmersion t ∧ ∃ α : Oˣ, t =
      Spec.map (CommRingCat.ofHom (CrossingQuotient.lift ϖ (ϖ * ((α⁻¹ : Oˣ) : O)) (α : O)
        (by rw [mul_assoc, Units.inv_mul, mul_one]; rfl)).toRingHom) ≫ Resolution.ι ϖ e ⟨d - 1, by omega⟩ := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_Resolution_isClosedImmersion_and_exists_eq_specMap_lift_comp_iota_of_comp_toSpec_eq_id.solution
