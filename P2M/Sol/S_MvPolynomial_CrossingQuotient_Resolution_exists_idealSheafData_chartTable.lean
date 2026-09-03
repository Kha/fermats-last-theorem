import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_comap_iota_vanishingIdeal_closure_lines
import P2M.Util
namespace P2MW.S_MvPolynomial_CrossingQuotient_Resolution_exists_idealSheafData_chartTable
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

universe u

open MvPolynomial MvPolynomial.CrossingQuotient MvPolynomial.CrossingQuotient.Resolution in
theorem solution {W : Type u} [CommRing W] (t : W) (e : ℕ) [IsReduced (W ⧸ Ideal.span {t})] :
    ∃ F : Fin (e + 1) → (Resolution t e).IdealSheafData,
      ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (ι t e i) =
        Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W t))).inv.hom
          (if (k : ℕ) = (i : ℕ) then Ideal.span {V t} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U t} else ⊤)) :=
  ⟨fun k => Scheme.IdealSheafData.vanishingIdeal ⟨closure
        ((⋃ (j : Fin e) (_ : (j : ℕ) + 1 = (k : ℕ)), (Resolution.ι t e j) '' (PrimeSpectrum.zeroLocus {U t})) ∪
         (⋃ (j : Fin e) (_ : (j : ℕ) = (k : ℕ)), (Resolution.ι t e j) '' (PrimeSpectrum.zeroLocus {V t}))),
        isClosed_closure⟩,
    fun i k => comap_iota_vanishingIdeal_closure_lines t e i (k : ℕ)⟩
