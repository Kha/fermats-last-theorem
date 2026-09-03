import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_BaseChange
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_mulEquiv_point_baseChange_and_addEquiv_points_baseChange

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.exists_mulEquiv_point_baseChange_and_addEquiv_points_baseChange
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
    (S : Type) [CommRing S] [Algebra R S] [Nontrivial S]
    (L : Type) [CommRing L] [Algebra R L] [Algebra S L] [IsScalarTower R S L] :
    ∃ (e : ∀ v : ℕ, G.Point L v ≃* (G.baseChange S).Point L v)
      (E : G.Points L ≃+ (G.baseChange S).Points L),
      (∀ (v : ℕ) (x : G.Point L v) (s : S) (a : G.level v),
        PDivisibleGroup.Point.toAlgHom (e v x) (s ⊗ₜ[R] a) = s • PDivisibleGroup.Point.toAlgHom x a) ∧
      (∀ (v : ℕ) (x : G.Point L v),
        E (G.pointsMkAdd L v (Additive.ofMul x)) = (G.baseChange S).pointsMkAdd L v (Additive.ofMul (e v x))) ∧
      (∀ (σ : L ≃ₐ[S] L) (v : ℕ) (x : G.Point L v),
        e v (G.pointMap ((σ.restrictScalars R : L ≃ₐ[R] L) : L →ₐ[R] L) v x) =
          (G.baseChange S).pointMap (σ : L →ₐ[S] L) v (e v x)) ∧
      (∀ (σ : L ≃ₐ[S] L) (z : G.Points L), E ((σ.restrictScalars R : L ≃ₐ[R] L) • z) = σ • E z) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_mulEquiv_point_baseChange_and_addEquiv_points_baseChange.solution
