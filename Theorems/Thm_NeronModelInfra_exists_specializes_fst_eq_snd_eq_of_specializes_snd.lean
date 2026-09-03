import Mathlib
import P2M.Util
import P2M.Sol.S_NeronModelInfra_exists_specializes_fst_eq_snd_eq_of_specializes_snd

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem NeronModelInfra.exists_specializes_fst_eq_snd_eq_of_specializes_snd
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (θ : ↑(pullback f f)) (hθ : f.base ((pullback.fst f f).base θ) = IsLocalRing.closedPoint R)
    (y : X) (hy : y ⤳ (pullback.snd f f).base θ) (hys : f.base y = IsLocalRing.closedPoint R) :
    ∃ θ' : ↑(pullback f f), θ' ⤳ θ ∧ (pullback.fst f f).base θ' = (pullback.fst f f).base θ ∧
      (pullback.snd f f).base θ' = y := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_exists_specializes_fst_eq_snd_eq_of_specializes_snd.solution
