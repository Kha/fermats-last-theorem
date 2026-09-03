import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Pullback_eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Pullback.eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {t₁ t₂ : ↥(pullback f g)}
    (h₁ : (pullback.fst f g).base t₁ = (pullback.fst f g).base t₂)
    (h₂ : (pullback.snd f g).base t₁ = (pullback.snd f g).base t₂)
    [IsIso (f.residueFieldMap ((pullback.fst f g).base t₂))] :
    t₁ = t₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Pullback_eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap.solution
