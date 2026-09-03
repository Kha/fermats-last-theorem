import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_Resolution_mem_support_iff_eq_addVal_of_comp_toCrossing_eq
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

universe u

theorem MvPolynomial.CrossingQuotient.Resolution.mem_support_iff_eq_addVal_of_comp_toCrossing_eq
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}) (e : ℕ)
    (F : Fin (e + 1) → (Resolution ϖ e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (Resolution.ι ϖ e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O ϖ))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {V ϖ} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U ϖ} else ⊤)))
    (t : Spec (CommRingCat.of O) ⟶ Resolution ϖ e) (ht : t ≫ Resolution.toSpec ϖ e = 𝟙 _)
    (ψ : CrossingQuotient O (ϖ ^ e) →+* O)
    (hψ : t ≫ Resolution.toCrossing ϖ e = Spec.map (CommRingCat.ofHom ψ))
    (k : Fin (e + 1)) :
    t.base (IsLocalRing.closedPoint O) ∈ (F k).support ↔
      ((k : ℕ) : ℕ∞) = IsDiscreteValuationRing.addVal O (ψ (CrossingQuotient.U (ϖ ^ e))) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_Resolution_mem_support_iff_eq_addVal_of_comp_toCrossing_eq.solution
