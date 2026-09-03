import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isPullback_snd_specMap_algebraOfHom

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom
    {R : Type u} [CommRing R] {C T : Scheme.{u}} (c : C ⟶ Spec (.of R)) (t : T ⟶ Spec (.of R))
    (W : T.Opens) (hW : IsAffineOpen W) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom t W
    ∃ g' : Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)) ⟶ Limits.pullback c t,
      IsPullback g' (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W))) (Limits.pullback.snd c t)
        hW.fromSpec ∧
      g' ≫ Limits.pullback.fst c t = Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isPullback_snd_specMap_algebraOfHom.solution
