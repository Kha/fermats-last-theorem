import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_Resolution_U_mem_and_V_mem_asIdeal_toCrossing_of_mem_support
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

universe u

theorem MvPolynomial.CrossingQuotient.Resolution.U_mem_and_V_mem_asIdeal_toCrossing_of_mem_support
    {W : Type u} [CommRing W] (t : W) (e : ℕ)
    (F : Fin (e + 1) → (Resolution t e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (ι t e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W t))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {V t} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U t} else ⊤)))
    (k : ℕ) (hk0 : 0 < k) (hke : k < e) (z : Resolution t e) (hz : z ∈ (F ⟨k, by omega⟩).support) :
    U (t ^ e) ∈ ((toCrossing t e).base z).asIdeal ∧ V (t ^ e) ∈ ((toCrossing t e).base z).asIdeal := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_Resolution_U_mem_and_V_mem_asIdeal_toCrossing_of_mem_support.solution
