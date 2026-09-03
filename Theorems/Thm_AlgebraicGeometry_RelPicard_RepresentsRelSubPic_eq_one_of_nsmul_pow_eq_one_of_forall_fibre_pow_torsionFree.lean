import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_eq_one_of_nsmul_pow_eq_one_of_forall_fibre_pow_torsionFree

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.eq_one_of_nsmul_pow_eq_one_of_forall_fibre_pow_torsionFree
    {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of ℤ))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) c)
    (D : RelativePic0Designation ℤ c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D) (p : ℕ)

    (htors : ∀ (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (k : ℕ),
      letI := (algEquivZeroGroupCut c ε).commGroupObj (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))))
      ∀ ξ : (relSubPicPresheaf c ε (algEquivZeroGroupCut c ε).toSubPicCondition).obj
          (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))))), ξ ^ (p ^ k) = 1 → ξ = 1)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (k : ℕ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))) D.toBase)
    (hx : hD.relativeGroupLaw.nsmul _ (p ^ k) x = hD.relativeGroupLaw.one _) :
    x = hD.relativeGroupLaw.one _ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_eq_one_of_nsmul_pow_eq_one_of_forall_fibre_pow_torsionFree.solution
