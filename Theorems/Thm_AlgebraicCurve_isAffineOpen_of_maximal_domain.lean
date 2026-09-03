import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_isAffineOpen_of_maximal_domain

universe u

open CategoryTheory AlgebraicGeometry Polynomial

theorem AlgebraicCurve.isAffineOpen_of_maximal_domain
    {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (U : C.Opens) [Nonempty U] (s : Γ(C, U))
    (hU : ∀ x : C, C.germToFunctionField U s ∈
      (algebraMap (C.presheaf.stalk x) C.functionField).range → x ∈ U)
    (hs : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      Transcendental k (C.germToFunctionField U s)) :
    IsAffineOpen U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_isAffineOpen_of_maximal_domain.solution
