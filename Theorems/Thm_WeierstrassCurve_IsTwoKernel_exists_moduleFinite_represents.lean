import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_IsTwoKernel_exists_moduleFinite_represents

set_option autoImplicit false

universe u

open Polynomial

theorem WeierstrassCurve.IsTwoKernel.exists_moduleFinite_represents
    {B : Type u} [CommRing B] (W : WeierstrassCurve B) (h2 : IsUnit ((2 : ℕ) : B)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra B C) (_ : Module.Finite B C) (hᵤ : Polynomial C)
      (_ : (W.map (algebraMap B C)).IsTwoKernel hᵤ),
      ∀ (T : Type u) [CommRing T] (φ : B →+* T) (h : Polynomial T),
        (W.map φ).IsTwoKernel h ↔
          ∃! ψ : C →+* T, ψ.comp (algebraMap B C) = φ ∧ hᵤ.map ψ = h := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_IsTwoKernel_exists_moduleFinite_represents.solution
