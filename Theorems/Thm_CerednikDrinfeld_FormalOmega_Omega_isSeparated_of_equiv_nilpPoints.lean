import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_Omega_isSeparated_of_equiv_nilpPoints

set_option autoImplicit false

open CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic TensorProduct

open CategoryTheory AlgebraicGeometry

theorem CerednikDrinfeld.FormalOmega.Omega.isSeparated_of_equiv_nilpPoints
    (p : ℕ) [Fact p.Prime]
    (C : Type) [CommRing C] [Algebra ℤ_[p] C]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of C))
    (pt : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] C S],
      (Omega ℚ_[p] (p : ℤ_[p])).obj S ≃ (Scheme.nilpPoints f).obj S)
    (hpt : ∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] C S]
        [CommRing S'] [Algebra C S'] [Algebra ℤ_[p] S'] [IsScalarTower ℤ_[p] C S']
        (φ : S →ₐ[C] S') (d : (Omega ℚ_[p] (p : ℤ_[p])).obj S),
        pt S' ((Omega ℚ_[p] (p : ℤ_[p])).map (φ.restrictScalars ℤ_[p]) d) = (Scheme.nilpPoints f).map φ (pt S d)) :
    IsSeparated f := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_Omega_isSeparated_of_equiv_nilpPoints.solution
