import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_bijective_appTop_of_forall_isMaximal

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem AlgebraicGeometry.bijective_appTop_of_forall_isMaximal
    {X : Scheme.{u}} {R : CommRingCat.{u}} (q : X ⟶ Spec R) [CompactSpace X] [QuasiSeparatedSpace X]
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      Function.Bijective (pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime P))))).appTop) :
    Function.Bijective q.appTop := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_bijective_appTop_of_forall_isMaximal.solution
