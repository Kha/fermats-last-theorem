import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_exists_ringEquiv_zChartAwayDegreeZero

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem WeierstrassProjModel.exists_ringEquiv_zChartAwayDegreeZero (R : Type) [CommRing R] :
    (∃ e : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
          (X 2 : MvPolynomial (Fin 3) R) ≃+*
        Polynomial (Polynomial R),
      ∀ (n : ℕ) (a : MvPolynomial (Fin 3) R)
        (ha : a ∈ homogeneousSubmodule (Fin 3) R (n • 1)),
        e (HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 3) R)
            ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ 2)) n a ha)
          = aeval (![Polynomial.C Polynomial.X, Polynomial.X, 1] :
              Fin 3 → Polynomial (Polynomial R)) a) ∧
    ∀ (V : WeierstrassCurve.Projective R),
      aeval (![Polynomial.C Polynomial.X, Polynomial.X, 1] :
          Fin 3 → Polynomial (Polynomial R)) V.polynomial
        = V.toAffine.polynomial := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_exists_ringEquiv_zChartAwayDegreeZero.solution
