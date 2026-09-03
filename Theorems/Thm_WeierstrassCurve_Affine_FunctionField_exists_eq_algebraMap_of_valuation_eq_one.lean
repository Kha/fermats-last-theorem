import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_FunctionField_exists_eq_algebraMap_of_valuation_eq_one

theorem WeierstrassCurve.Affine.FunctionField.exists_eq_algebraMap_of_valuation_eq_one {F : Type*} [Field F] {W : WeierstrassCurve F} [IsDedekindDomain W.toAffine.CoordinateRing] {f : W.toAffine.FunctionField} (hf : ∀ v : IsDedekindDomain.HeightOneSpectrum W.toAffine.CoordinateRing, v.valuation W.toAffine.FunctionField f = 1) : ∃ c : F, c ≠ 0 ∧ f = algebraMap F W.toAffine.FunctionField c := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_FunctionField_exists_eq_algebraMap_of_valuation_eq_one.solution
