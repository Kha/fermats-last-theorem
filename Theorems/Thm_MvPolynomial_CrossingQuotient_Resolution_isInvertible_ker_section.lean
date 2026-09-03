import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_Resolution_isInvertible_ker_section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

universe u

theorem MvPolynomial.CrossingQuotient.Resolution.isInvertible_ker_section
    {O : Type u} [CommRing O] (ϖ : O) (e : ℕ) (hϖ : ϖ ∈ nonZeroDivisors O)
    (d : ℕ) (hd0 : 0 < d) (hde : d < e) (α : Oˣ) :
    (Spec.map (CommRingCat.ofHom (CrossingQuotient.lift ϖ (ϖ * ((α⁻¹ : Oˣ) : O)) (α : O)
        (by rw [mul_assoc, Units.inv_mul, mul_one]; rfl)).toRingHom) ≫ Resolution.ι ϖ e ⟨d - 1, by omega⟩).ker.IsInvertible := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_Resolution_isInvertible_ker_section.solution
