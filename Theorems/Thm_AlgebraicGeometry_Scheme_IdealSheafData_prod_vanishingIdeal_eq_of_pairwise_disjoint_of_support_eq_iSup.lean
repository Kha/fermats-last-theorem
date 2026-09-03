import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_prod_vanishingIdeal_eq_of_pairwise_disjoint_of_support_eq_iSup

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.IdealSheafData.prod_vanishingIdeal_eq_of_pairwise_disjoint_of_support_eq_iSup
    {Y : Scheme.{u}} {ι : Type*} [Fintype ι] (Z : ι → Closeds Y)
    (hdisj : Pairwise fun i j => Disjoint (Z i) (Z j))
    (J : Y.IdealSheafData) (hrad : J.radical = J) (hsupp : J.support = ⨆ i, Z i) :
    ∏ i, Scheme.IdealSheafData.vanishingIdeal (Z i) = J := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_prod_vanishingIdeal_eq_of_pairwise_disjoint_of_support_eq_iSup.solution
