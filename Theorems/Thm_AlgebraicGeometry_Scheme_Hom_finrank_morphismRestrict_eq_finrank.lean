import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_finrank_morphismRestrict_eq_finrank

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.finrank_morphismRestrict_eq_finrank
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] (W : S.Opens) [Flat (f ∣_ W)] (s : S) (hs : s ∈ W) :
    (f ∣_ W).finrank ⟨s, hs⟩ = f.finrank s := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_finrank_morphismRestrict_eq_finrank.solution
