import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_mulEquiv_point_addEquiv_points_eq_pointMap_of_isAlgClosed

set_option autoImplicit false

theorem PDivisibleGroup.exists_mulEquiv_point_addEquiv_points_eq_pointMap_of_isAlgClosed
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
    (L : Type) [Field L] [IsAlgClosed L] [Algebra R L] (L' : Type) [Field L'] [Algebra R L'] (j : L →ₐ[R] L') :
    ∃ (e : ∀ v : ℕ, G.Point L v ≃* G.Point L' v) (E : G.Points L ≃+ G.Points L'),
      (∀ (v : ℕ) (x : G.Point L v), e v x = G.pointMap j v x) ∧
      (∀ z : G.Points L, E z = G.pointsMap j z) ∧
      (∀ (v : ℕ) (x : G.Point L v),
        E (G.pointsMkAdd L v (Additive.ofMul x)) = G.pointsMkAdd L' v (Additive.ofMul (e v x))) ∧
      (∀ (σ : L ≃ₐ[R] L) (σ' : L' ≃ₐ[R] L'), (∀ a : L, j (σ a) = σ' (j a)) →
        ∀ z : G.Points L, E (σ • z) = σ' • E z) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_mulEquiv_point_addEquiv_points_eq_pointMap_of_isAlgClosed.solution
