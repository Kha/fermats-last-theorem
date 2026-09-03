import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_le_isNilpotent_mem_ideal_of_le_nilradical

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.exists_le_isNilpotent_mem_ideal_of_le_nilradical
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (hI : I ≤ X.nilradical) (U : X.affineOpens) (s : Γ(X, U))
    (hs : s ∈ I.ideal U) :
    ∃ J : X.IdealSheafData, J ≤ I ∧ IsNilpotent J ∧ s ∈ J.ideal U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_le_isNilpotent_mem_ideal_of_le_nilradical.solution
