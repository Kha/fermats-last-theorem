import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isAffineOpen_of_isAffineOpen_preimage_of_isPullback_of_flat

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isAffineOpen_of_isAffineOpen_preimage_of_isPullback_of_flat
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (π : 𝒪) (hπ : Irreducible π)
    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (hflat : ∀ n : ℕ, Flat (xb n))
    (n : ℕ) (U : (X (n + 1)).Opens) (hU : IsAffineOpen ((xt n) ⁻¹ᵁ U)) : IsAffineOpen U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isAffineOpen_of_isAffineOpen_preimage_of_isPullback_of_flat.solution
