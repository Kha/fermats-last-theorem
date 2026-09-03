import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_nsmul_eq_one_not_dvd_of_forall_fibre_exists_pow_eq_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_nsmul_eq_one_not_dvd_of_forall_fibre_exists_pow_eq_one
    {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of ℤ))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) c)
    (D : RelativePic0Designation ℤ c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D) (p : ℕ)

    (hfin : ∀ (K : Type) [Field K] [CharP K p] [IsAlgClosed K], (∀ u : Kˣ, IsOfFinOrder u) →
      letI := (algEquivZeroGroupCut c ε).commGroupObj (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))))
      ∀ ξ : (relSubPicPresheaf c ε (algEquivZeroGroupCut c ε).toSubPicCondition).obj
          (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))))),
        ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ ξ ^ m = 1)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (hK : ∀ u : Kˣ, IsOfFinOrder u)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))) D.toBase) :
    ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ hD.relativeGroupLaw.nsmul _ m x = hD.relativeGroupLaw.one _ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_nsmul_eq_one_not_dvd_of_forall_fibre_exists_pow_eq_one.solution
