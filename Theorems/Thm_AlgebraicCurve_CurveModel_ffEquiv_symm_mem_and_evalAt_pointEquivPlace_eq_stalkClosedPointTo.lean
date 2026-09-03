import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry AlgebraicCurve
universe u v

theorem AlgebraicCurve.CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]
    (M : CurveModel K L) (pt : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _})
    (s : M.C.presheaf.stalk (pt.1.base (IsLocalRing.closedPoint K))) :
    ∃ h : M.ffEquiv.symm (algebraMap _ M.C.functionField s) ∈ (M.pointEquivPlace pt).toValuationSubring,
      IsLocalRing.residue (M.pointEquivPlace pt).toValuationSubring ⟨_, h⟩ =
        algebraMap K (M.pointEquivPlace pt).ResidueField ((Scheme.stalkClosedPointTo pt.1).hom s) ∧
      (M.pointEquivPlace pt).evalAt (M.ffEquiv.symm (algebraMap _ M.C.functionField s)) =
        (Scheme.stalkClosedPointTo pt.1).hom s := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo.solution
