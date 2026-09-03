import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_IsCyclicGenKernel_exists_moduleFinite_represents

set_option autoImplicit false

universe u

theorem WeierstrassCurve.IsCyclicGenKernel.exists_moduleFinite_represents
    {B : Type u} [CommRing B] (W : WeierstrassCurve B) (p k : ℕ) [Fact p.Prime] (hpk : 3 ≤ p ^ k)
    (hu : IsUnit ((p : B) * W.Δ)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra B C) (_ : Module.Finite B C) (hᵤ : Polynomial C)
      (_ : (W.map (algebraMap B C)).IsCyclicGenKernel p k hᵤ),
      ∀ (T : Type u) [CommRing T] (φ : B →+* T) (h : Polynomial T),
        (W.map φ).IsCyclicGenKernel p k h ↔
          ∃! ψ : C →+* T, ψ.comp (algebraMap B C) = φ ∧ hᵤ.map ψ = h := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_IsCyclicGenKernel_exists_moduleFinite_represents.solution
