import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_comap_sectionIdeal_eq_top_and_finrank_eq_zero_of_forall_notMem_support

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.comap_sectionIdeal_eq_top_and_finrank_eq_zero_of_forall_notMem_support
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (σ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {k : Type u} [Field k] (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (J : (pullback c t).IdealSheafData)
    (hJ : ∀ x ∈ Set.range (rigSection c t σ), x ∉ J.support) :
    (sectionIdeal c σ t).comap J.subschemeι = ⊤ ∧
      ((sectionIdeal c σ t).comap J.subschemeι).IsInvertible ∧
      IsFinite (((sectionIdeal c σ t).comap J.subschemeι).subschemeι ≫ J.subschemeι ≫ pullback.snd c t) ∧
      ∀ q : Spec (CommRingCat.of k),
        (((sectionIdeal c σ t).comap J.subschemeι).subschemeι ≫ J.subschemeι ≫ pullback.snd c t).finrank q = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_comap_sectionIdeal_eq_top_and_finrank_eq_zero_of_forall_notMem_support.solution
