import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_Resolution_exists_idealSheafData_chartTable
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

universe u

theorem MvPolynomial.CrossingQuotient.Resolution.exists_idealSheafData_chartTable
    {W : Type u} [CommRing W] (t : W) (e : ℕ) [IsReduced (W ⧸ Ideal.span {t})] :
    ∃ F : Fin (e + 1) → (Resolution t e).IdealSheafData,
      ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (ι t e i) =
        Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W t))).inv.hom
          (if (k : ℕ) = (i : ℕ) then Ideal.span {V t} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U t} else ⊤)) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_Resolution_exists_idealSheafData_chartTable.solution
