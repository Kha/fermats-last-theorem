import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_isInvertible_ideal_eq_span_of_locallyPrincipalDatum

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.exists_isInvertible_ideal_eq_span_of_locallyPrincipalDatum
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.affineOpens) (hU : ⨆ i, (U i : X.Opens) = ⊤)
    (g : ∀ i, Γ(X, U i))
    (hg : ∀ (i : ι) (W : X.affineOpens) (h : (W : X.Opens) ≤ U i),
      (X.presheaf.map (homOfLE h).op).hom (g i) ∈ nonZeroDivisors Γ(X, W))
    (hcomp : ∀ (i j : ι) (W : X.affineOpens) (hi : (W : X.Opens) ≤ U i) (hj : (W : X.Opens) ≤ U j),
      Ideal.span {(X.presheaf.map (homOfLE hi).op).hom (g i)} = Ideal.span {(X.presheaf.map (homOfLE hj).op).hom (g j)}) :
    ∃ I : X.IdealSheafData, I.IsInvertible ∧
      ∀ (i : ι) (W : X.affineOpens) (h : (W : X.Opens) ≤ U i),
        I.ideal W = Ideal.span {(X.presheaf.map (homOfLE h).op).hom (g i)} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_isInvertible_ideal_eq_span_of_locallyPrincipalDatum.solution
