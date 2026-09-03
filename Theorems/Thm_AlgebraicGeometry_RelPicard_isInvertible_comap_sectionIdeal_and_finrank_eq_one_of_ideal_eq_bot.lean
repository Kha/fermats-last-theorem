import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_isInvertible_comap_sectionIdeal_and_finrank_eq_one_of_ideal_eq_bot

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry open AlgebraicGeometry.RelPicard hiding isInvertible_sectionIdeal_of_range_subset open NeronModelInfra

theorem AlgebraicGeometry.RelPicard.isInvertible_comap_sectionIdeal_and_finrank_eq_one_of_ideal_eq_bot
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (σ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hσ : Set.range σ.1 ⊆ (U : Set C))
    {k : Type u} [Field k] (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (J : (pullback c t).IdealSheafData)
    (hJ : ∃ V : (pullback c t).affineOpens,
      Set.range (rigSection c t σ) ⊆ ((V : (pullback c t).Opens) : Set ↥(pullback c t)) ∧ J.ideal V = ⊥) :
    ((sectionIdeal c σ t).comap J.subschemeι).IsInvertible ∧
      IsFinite (((sectionIdeal c σ t).comap J.subschemeι).subschemeι ≫ J.subschemeι ≫ pullback.snd c t) ∧
      ∀ q : Spec (CommRingCat.of k),
        (((sectionIdeal c σ t).comap J.subschemeι).subschemeι ≫ J.subschemeι ≫ pullback.snd c t).finrank q = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_isInvertible_comap_sectionIdeal_and_finrank_eq_one_of_ideal_eq_bot.solution
