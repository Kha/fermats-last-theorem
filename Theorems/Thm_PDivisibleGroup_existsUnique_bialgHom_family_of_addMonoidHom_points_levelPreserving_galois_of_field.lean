import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_field

set_option autoImplicit false

theorem PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_field
    (p : ℕ) [Fact p.Prime]
    {K : Type} [Field K] [CharZero K]
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    {h h' : ℕ} (G : PDivisibleGroup K p h) (H : PDivisibleGroup K p h')
    (F : G.Points L →+ H.Points L)

    (hFlev : ∀ (v : ℕ) (x : G.Point L v), ∃ y : H.Point L v,
      F (G.pointsMkAdd L v (Additive.ofMul x)) = H.pointsMkAdd L v (Additive.ofMul y))

    (hFgal : ∀ (τ : L ≃ₐ[K] L) (z : G.Points L), F (τ • z) = τ • F z) :
    ∃ φ : ∀ v : ℕ, H.level v →ₐc[K] G.level v,
      (∀ v : ℕ, (G.transition v).comp (φ (v + 1)) = (φ v).comp (H.transition v)) ∧
      (∀ (v : ℕ) (x : G.Point L v),
        F (G.pointsMkAdd L v (Additive.ofMul x)) =
          H.pointsMkAdd L v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : H.level v →ₐ[K] G.level v))))) ∧

      (∀ φ' : ∀ v : ℕ, H.level v →ₐc[K] G.level v,
        (∀ (v : ℕ) (x : G.Point L v),
          F (G.pointsMkAdd L v (Additive.ofMul x)) =
            H.pointsMkAdd L v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
              ((PDivisibleGroup.Point.toAlgHom x).comp (φ' v : H.level v →ₐ[K] G.level v))))) →
        φ' = φ) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_field.solution
