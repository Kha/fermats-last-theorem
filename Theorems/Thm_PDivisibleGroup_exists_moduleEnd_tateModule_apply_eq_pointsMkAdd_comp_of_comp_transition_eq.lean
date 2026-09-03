import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_moduleEnd_tateModule_apply_eq_pointsMkAdd_comp_of_comp_transition_eq

set_option autoImplicit false

theorem PDivisibleGroup.exists_moduleEnd_tateModule_apply_eq_pointsMkAdd_comp_of_comp_transition_eq
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] {L : Type} [CommRing L] [Algebra O L]
    {h : ℕ} (G : PDivisibleGroup O p h)
    (u : ∀ v : ℕ, G.level v →ₐc[O] G.level v)
    (hu : ∀ v : ℕ, (G.transition v).comp (u (v + 1)) = (u v).comp (G.transition v)) :
    ∃ U : Module.End ℤ_[p] (TateModule p (G.Points L)),
      ∀ (x : TateModule p (G.Points L)) (n w : ℕ) (f : G.Point L w),
        G.pointsMkAdd L w (Additive.ofMul f) = (x : ℕ → G.Points L) n →
        ((U x : TateModule p (G.Points L)) : ℕ → G.Points L) n =
          G.pointsMkAdd L w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp (u w : G.level w →ₐ[O] G.level w)))) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_moduleEnd_tateModule_apply_eq_pointsMkAdd_comp_of_comp_transition_eq.solution
