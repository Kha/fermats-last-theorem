import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : Λ.FG) (N : ℕ)
    (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K)
      (E₀ : FakeEllipticCurve Λ N K),
      FakeEllipticCurve.IsPullback (algebraMap K (AlgebraicClosure ℚ)) E₀ E := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg.solution
