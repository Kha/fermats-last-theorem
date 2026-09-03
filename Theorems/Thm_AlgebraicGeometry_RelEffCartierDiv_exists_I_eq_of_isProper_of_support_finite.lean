import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_of_isProper_of_support_finite

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_of_isProper_of_support_finite
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    (I : (pullback f x).IdealSheafData) (hfin : (I.support : Set ↥(pullback f x)).Finite) :
    ∃ (r : ℕ) (D : RelEffCartierDiv f r x), D.I = I := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_of_isProper_of_support_finite.solution
