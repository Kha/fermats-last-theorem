import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_maximalIdeal_stalk_eq_span_germ_V_sub

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial

theorem MvPolynomial.CrossingQuotient.maximalIdeal_stalk_eq_span_germ_V_sub
    (W : Type u) [CommRing W] [IsDomain W] (t x' y' : W) (hxy : x' * y' = t) (hy : y' ≠ 0) :
    letI Q := CrossingQuotient W t
    letI M : Scheme.{u} := Spec (CommRingCat.of Q)
    letI φ : Q →+* Γ(M, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
    letI L : Q →+* W := (CrossingQuotient.lift (t := t) x' y' (by rw [Algebra.algebraMap_self, RingHom.id_apply, hxy])).toRingHom
    ∀ (hprime : (RingHom.ker L).IsPrime),
    letI m : M := (⟨RingHom.ker L, hprime⟩ : PrimeSpectrum Q)
    IsLocalRing.maximalIdeal (M.presheaf.stalk m) =
      Ideal.span {M.presheaf.germ ⊤ m trivial (φ (CrossingQuotient.V t - algebraMap W Q y'))} := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_maximalIdeal_stalk_eq_span_germ_V_sub.solution
