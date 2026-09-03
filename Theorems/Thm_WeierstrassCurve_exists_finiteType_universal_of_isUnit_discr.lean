import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_finiteType_universal_of_isUnit_discr

set_option autoImplicit false

universe u

theorem WeierstrassCurve.exists_finiteType_universal_of_isUnit_discr (A : Type u) [CommRing A] :
    ∃ (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra A S₀) (_ : Algebra.FiniteType A S₀)
      (W₀ : WeierstrassCurve S₀) (_ : IsUnit W₀.Δ),
      ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T), IsUnit W.Δ →
        ∃! ψ : S₀ →ₐ[A] T, W₀.map ψ.toRingHom = W := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_finiteType_universal_of_isUnit_discr.solution
