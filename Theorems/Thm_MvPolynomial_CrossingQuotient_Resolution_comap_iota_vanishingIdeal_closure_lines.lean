import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_Resolution_comap_iota_vanishingIdeal_closure_lines

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

universe u

theorem MvPolynomial.CrossingQuotient.Resolution.comap_iota_vanishingIdeal_closure_lines
    {W : Type u} [CommRing W] (t : W) (e : ℕ) [IsReduced (W ⧸ Ideal.span {t})] (i : Fin e) (k : ℕ) :
    (Scheme.IdealSheafData.vanishingIdeal ⟨closure
        ((⋃ (j : Fin e) (_ : (j : ℕ) + 1 = k), (Resolution.ι t e j) '' (PrimeSpectrum.zeroLocus {U t})) ∪
         (⋃ (j : Fin e) (_ : (j : ℕ) = k), (Resolution.ι t e j) '' (PrimeSpectrum.zeroLocus {V t}))),
        isClosed_closure⟩).comap (Resolution.ι t e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W t))).inv.hom
        (if k = (i : ℕ) then Ideal.span {V t} else if k = (i : ℕ) + 1 then Ideal.span {U t} else ⊤)) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_Resolution_comap_iota_vanishingIdeal_closure_lines.solution
