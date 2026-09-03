import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_exists_section_basicOpen_sup_mul_eq_of_mul_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

theorem MvPolynomial.CrossingQuotient.exists_section_basicOpen_sup_mul_eq_of_mul_eq
    (W : Type u) [CommRing W] (t x' y' : W) (hxy : x' * y' = t) (w : Wˣ) :
    letI M : Scheme.{u} := Spec (CommRingCat.of (CrossingQuotient W t))
    letI φ : CrossingQuotient W t →+* Γ(M, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W t))).inv.hom
    letI a : Γ(M, ⊤) := φ (CrossingQuotient.U t - algebraMap W _ x')
    letI b : Γ(M, ⊤) := φ (algebraMap W _ y' - CrossingQuotient.V t)
    letI aw : Γ(M, ⊤) := φ (CrossingQuotient.U t - algebraMap W _ ((w : W) * x'))
    letI bw : Γ(M, ⊤) := φ (algebraMap W _ y' - algebraMap W _ (w : W) * CrossingQuotient.V t)
    ∃ g : Γ(M, M.basicOpen a ⊔ M.basicOpen b),

      M.presheaf.map (homOfLE (le_sup_left : M.basicOpen a ≤ M.basicOpen a ⊔ M.basicOpen b)).op g *
          M.presheaf.map (homOfLE (le_top : M.basicOpen a ≤ ⊤)).op a =
        M.presheaf.map (homOfLE (le_top : M.basicOpen a ≤ ⊤)).op aw ∧

      M.presheaf.map (homOfLE (le_sup_right : M.basicOpen b ≤ M.basicOpen a ⊔ M.basicOpen b)).op g *
          M.presheaf.map (homOfLE (le_top : M.basicOpen b ≤ ⊤)).op b =
        M.presheaf.map (homOfLE (le_top : M.basicOpen b ≤ ⊤)).op bw ∧

      IsUnit (M.presheaf.map (homOfLE (inf_le_left :
          (M.basicOpen a ⊔ M.basicOpen b) ⊓ (M.basicOpen aw ⊔ M.basicOpen bw) ≤ M.basicOpen a ⊔ M.basicOpen b)).op g) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_exists_section_basicOpen_sup_mul_eq_of_mul_eq.solution
