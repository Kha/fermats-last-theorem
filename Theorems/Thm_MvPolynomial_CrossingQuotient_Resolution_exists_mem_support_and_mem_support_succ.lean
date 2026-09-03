import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_Resolution_exists_mem_support_and_mem_support_succ
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

universe u

theorem MvPolynomial.CrossingQuotient.Resolution.exists_mem_support_and_mem_support_succ
    {W : Type u} [CommRing W] (t : W) (e : ℕ) (ht : ¬ IsUnit t)
    (F : Fin (e + 1) → (Resolution t e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (ι t e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W t))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {V t} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U t} else ⊤)))
    (k : ℕ) (hke : k < e) :
    ∃ z : Resolution t e, z ∈ (F ⟨k, by omega⟩).support ∧ z ∈ (F ⟨k + 1, by omega⟩).support := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_Resolution_exists_mem_support_and_mem_support_succ.solution
