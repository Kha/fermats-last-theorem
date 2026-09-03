import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq

set_option autoImplicit false

universe u v

theorem ModularCurve.LevelP.TorsionPointRing.exists_ringHom_apply_torsionPt_eq
    {B : Type u} {A : Type v} [CommRing B] [CommRing A] (W : WeierstrassCurve B) (p : ℕ)
    (φ : B →+* A) (x y : A) (hxy : (W.map φ).toAffine.Equation x y)
    (hx : ((W.map φ).preΨ p).eval x = 0) :
    ∃ ψ : ModularCurve.LevelP.TorsionPointRing W p →+* A,
      ψ.comp (ModularCurve.LevelP.TorsionPointRing.ofBase W p) = φ ∧
        ψ (ModularCurve.LevelP.torsionPtX W p) = x ∧ ψ (ModularCurve.LevelP.torsionPtY W p) = y := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.solution
