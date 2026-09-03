import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_ringEquiv_quotient_sections_of_isPullback_of_flat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_ringEquiv_quotient_sections_of_isPullback_of_flat
    (S : Type) [CommRing S] (ϖ : S) (hϖ : ∀ s : S, ϖ * s = 0 → s = 0)
    (X' : ℕ → Scheme.{0}) (xb' : ∀ n : ℕ, X' n ⟶ Spec (CommRingCat.of (S ⧸ Ideal.span {ϖ ^ (n + 1)})))
    (xt' : ∀ n : ℕ, X' n ⟶ X' (n + 1))
    (hcart' : ∀ n : ℕ, IsPullback (xt' n) (xb' n) (xb' (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ (n + 1))))))))
    (hflat' : ∀ n : ℕ, Flat (xb' n))
    (G : Type) [Group G] [Finite G] (a' : ∀ n : ℕ, G →* Aut (X' n))
    (ha'_over : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ xb' n = xb' n)
    (ha'_xt : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ xt' n = xt' n ≫ (a' (n + 1) g).hom)
    (W' : ∀ n : ℕ, (X' n).Opens) (hW'a : ∀ n : ℕ, IsAffineOpen (W' n))
    (hW'c : ∀ n : ℕ, (xt' n) ⁻¹ᵁ (W' (n + 1)) = W' n)
    (hW's : ∀ (n : ℕ) (g : G), (a' n g).hom ⁻¹ᵁ (W' n) = W' n) :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra S R') (_ : MulSemiringAction G R') (_ : SMulCommClass G S R'),
      IsAdicComplete (Ideal.span {algebraMap S R' ϖ}) R' ∧
      (∀ x : R', algebraMap S R' ϖ * x = 0 → x = 0) ∧
      ∃ (lvl' : ∀ n : ℕ, (R' ⧸ Ideal.span {algebraMap S R' ϖ ^ (n + 1)}) ≃+* Γ(X' n, W' n)),
        (∀ (n : ℕ) (x : R'), (xt' n).appLE (W' (n + 1)) (W' n) (by rw [hW'c])
            (lvl' (n + 1) (Ideal.Quotient.mk _ x)) = lvl' n (Ideal.Quotient.mk _ x)) ∧
        (∀ (n : ℕ) (g : G) (x : R'), (a' n g⁻¹).hom.appLE (W' n) (W' n) (by rw [hW's])
            (lvl' n (Ideal.Quotient.mk _ x)) = lvl' n (Ideal.Quotient.mk _ (g • x))) ∧
        (∀ (n : ℕ) (s : S), lvl' n (Ideal.Quotient.mk _ (algebraMap S R' s)) =
            (xb' n).appLE ⊤ (W' n) le_top
              ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {ϖ ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_ringEquiv_quotient_sections_of_isPullback_of_flat.solution
