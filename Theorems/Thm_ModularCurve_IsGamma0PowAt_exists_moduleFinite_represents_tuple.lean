import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import P2M.Util
import P2M.Sol.S_ModularCurve_IsGamma0PowAt_exists_moduleFinite_represents_tuple

set_option autoImplicit false

universe u

open Polynomial

theorem ModularCurve.IsGamma0PowAt.exists_moduleFinite_represents_tuple
    {B : Type u} [CommRing B] (W : WeierstrassCurve B) (M' : ℕ)
    (hu : IsUnit (((M' : ℕ) : B) * W.Δ)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra B C) (_ : Module.Finite B C)
      (hᵤ : ↥M'.primeFactors → Polynomial C)
      (_ : ∀ p : ↥M'.primeFactors,
        ModularCurve.IsGamma0PowAt (W.map (algebraMap B C)) (p : ℕ) (M'.factorization (p : ℕ)) (hᵤ p)),
      ∀ (T : Type u) [CommRing T] (φ : B →+* T) (hh : ↥M'.primeFactors → Polynomial T),
        (∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt (W.map φ) (p : ℕ) (M'.factorization (p : ℕ)) (hh p)) ↔
          ∃! ψ : C →+* T, ψ.comp (algebraMap B C) = φ ∧ (fun p => (hᵤ p).map ψ) = hh := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IsGamma0PowAt_exists_moduleFinite_represents_tuple.solution
