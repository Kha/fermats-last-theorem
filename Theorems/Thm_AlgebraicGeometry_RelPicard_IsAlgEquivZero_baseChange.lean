import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_baseChange

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.IsAlgEquivZero.baseChange
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k)) {L : A.Modules} (hL : IsAlgEquivZero a L) :
    IsAlgEquivZero (pullback.snd a (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      ((Scheme.Modules.pullback (pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj L) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_baseChange.solution
