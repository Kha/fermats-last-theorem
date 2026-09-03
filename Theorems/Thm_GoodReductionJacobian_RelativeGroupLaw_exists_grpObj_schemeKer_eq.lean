import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_schemeKer_eq
attribute [-simp] GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

open CategoryTheory AlgebraicGeometry CategoryTheory.CartesianMonoidalCategory NeronModelInfra
  GoodReductionJacobian
open scoped CategoryTheory.MonObj

universe u
set_option maxHeartbeats 800000 in

theorem GoodReductionJacobian.RelativeGroupLaw.exists_grpObj_schemeKer_eq
    {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) :
    ∃ (_ : GrpObj (Over.mk (L.schemeKerStr n))) (_ : IsCommMonObj (Over.mk (L.schemeKerStr n))),
      ∃ pts : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
          (Over.mk t ⟶ Over.mk (L.schemeKerStr n)) ≃ L.torsionSubset t n,
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
            (a b : Over.mk t ⟶ Over.mk (L.schemeKerStr n)),
          (↑(pts t (a * b)) : SchemeHomOver t f) =
            L.mul t (↑(pts t a)) (↑(pts t b))) ∧
        (∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
            (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
            (a : Over.mk t ⟶ Over.mk (L.schemeKerStr n)),
          (↑(pts t' (Over.homMk (U := Over.mk t') (V := Over.mk t) ψ hψ ≫ a)) : SchemeHomOver t' f) =
            schemeHomOverComp ψ hψ (↑(pts t a))) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_schemeKer_eq.solution
