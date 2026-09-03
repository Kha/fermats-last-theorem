import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_isFinite_schemeKerStr_of_isPointsEval

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u

theorem WeierstrassProjModel.isFinite_schemeKerStr_of_isPointsEval
    {R : Type u} [CommRing R]
    (V : WeierstrassCurve.Projective R)
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
      Nonempty (pullback (projModelStrCR V)
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        ≅ projModelCR (V.baseChange K)))
    (G : RelativeGroupLaw R (projModelStrCR V))
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
        (V.baseChange F).toAffine.Point)
    (hev : IsPointsEval V G ev)
    (hℓ : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F] [IsAlgClosed F] (ℓ : ℕ),
      ℓ.Prime → (ℓ : F) ≠ 0 →
      ∃ P : (V.baseChange F).toAffine.Point, P ≠ 0 ∧ ℓ • P = 0)
    {n : ℕ} (hn : 0 < n) :
    IsFinite (G.schemeKerStr n) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_isFinite_schemeKerStr_of_isPointsEval.solution
