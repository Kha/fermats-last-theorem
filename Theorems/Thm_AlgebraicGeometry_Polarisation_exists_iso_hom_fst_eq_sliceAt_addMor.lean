import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_exists_iso_hom_fst_eq_sliceAt_addMor

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_iso_hom_fst_eq_sliceAt_addMor
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    {Y : Scheme.{0}} (fY : Y ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ A) (hjf : j ≫ f = fY) :
    ∃ Φ : pullback f fY ≅ pullback f fY,
      Φ.hom ≫ pullback.fst f fY = sliceAt f (⟨j, hjf⟩ : SchemeHomOver fY f) ≫ addMor f L ∧
      Φ.hom ≫ pullback.snd f fY = pullback.snd f fY := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_exists_iso_hom_fst_eq_sliceAt_addMor.solution
