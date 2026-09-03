import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_Resolution_prod_pow_eq_ofIdealTop_uSec_and_vSec_and_tSec
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

universe u

theorem MvPolynomial.CrossingQuotient.Resolution.prod_pow_eq_ofIdealTop_uSec_and_vSec_and_tSec
    {W : Type u} [CommRing W] (t : W) (e : ℕ)
    (F : Fin (e + 1) → (Resolution t e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (ι t e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W t))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {V t} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U t} else ⊤))) :
    (∏ k, F k ^ (k : ℕ) = Scheme.IdealSheafData.ofIdealTop (Ideal.span {(toCrossing t e).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W (t ^ e)))).inv.hom (U (t ^ e)))})) ∧
    (∏ k, F k ^ (e - (k : ℕ)) = Scheme.IdealSheafData.ofIdealTop (Ideal.span {(toCrossing t e).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W (t ^ e)))).inv.hom (V (t ^ e)))})) ∧
    (∏ k, F k = Scheme.IdealSheafData.ofIdealTop (Ideal.span {(toSpec t e).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom t)})) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_Resolution_prod_pow_eq_ofIdealTop_uSec_and_vSec_and_tSec.solution
