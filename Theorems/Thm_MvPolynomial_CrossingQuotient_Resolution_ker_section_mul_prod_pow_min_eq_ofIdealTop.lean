import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_Resolution_ker_section_mul_prod_pow_min_eq_ofIdealTop

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

universe u

theorem MvPolynomial.CrossingQuotient.Resolution.ker_section_mul_prod_pow_min_eq_ofIdealTop
    {O : Type u} [CommRing O] (ϖ : O) (e : ℕ)
    (F : Fin (e + 1) → (Resolution ϖ e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (Resolution.ι ϖ e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O ϖ))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {V ϖ} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U ϖ} else ⊤)))
    (d : ℕ) (hd0 : 0 < d) (hde : d < e) (α : Oˣ) :
    (Spec.map (CommRingCat.ofHom (CrossingQuotient.lift ϖ (ϖ * ((α⁻¹ : Oˣ) : O)) (α : O)
        (by rw [mul_assoc, Units.inv_mul, mul_one]; rfl)).toRingHom) ≫ Resolution.ι ϖ e ⟨d - 1, by omega⟩).ker *
        ∏ k : Fin (e + 1), F k ^ (min (k : ℕ) d) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {(Resolution.toCrossing ϖ e).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (ϖ ^ e)))).inv.hom
          (algebraMap O _ (ϖ ^ d) - algebraMap O _ (α : O) * CrossingQuotient.U (ϖ ^ e)))}) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_Resolution_ker_section_mul_prod_pow_min_eq_ofIdealTop.solution
