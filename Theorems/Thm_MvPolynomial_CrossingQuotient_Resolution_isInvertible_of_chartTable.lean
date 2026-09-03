import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_Resolution_isInvertible_of_chartTable
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

universe u

theorem MvPolynomial.CrossingQuotient.Resolution.isInvertible_of_chartTable
    {W : Type u} [CommRing W] (t : W) (e : ℕ)
    (hx : U t ∈ nonZeroDivisors (CrossingQuotient W t)) (hy : V t ∈ nonZeroDivisors (CrossingQuotient W t))
    (F : Fin (e + 1) → (Resolution t e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (ι t e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W t))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {V t} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U t} else ⊤)))
    (k : Fin (e + 1)) : (F k).IsInvertible := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_Resolution_isInvertible_of_chartTable.solution
