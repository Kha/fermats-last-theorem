import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_tower_baseChange_of_isPullback

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_tower_baseChange_of_isPullback
    (𝒪 : Type u) [CommRing 𝒪] (π : 𝒪)
    (X : ℕ → Scheme.{u}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (G : Type u) [Group G] (a : ∀ n : ℕ, G →* Aut (X n))
    (ha_over : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xb n = xb n)
    (ha_xt : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom)
    (S : Type u) [CommRing S] [Algebra 𝒪 S] :
    ∃ (X' : ℕ → Scheme.{u}) (xb' : ∀ n : ℕ, X' n ⟶ Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})))
      (xt' : ∀ n : ℕ, X' n ⟶ X' (n + 1)) (a' : ∀ n : ℕ, G →* Aut (X' n)) (q : ∀ n : ℕ, X' n ⟶ X n),
      (∀ n : ℕ, IsPullback (q n) (xb' n) (xb n)
        (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S)
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))))) ∧
      (∀ n : ℕ, IsPullback (xt' n) (xb' n) (xb' (n + 1))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
          (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 S π) (Nat.le_succ (n + 1)))))))) ∧
      (∀ n : ℕ, xt' n ≫ q (n + 1) = q n ≫ xt n) ∧
      (∀ (n : ℕ) (g : G), (a' n g).hom ≫ q n = q n ≫ (a n g).hom) ∧
      (∀ (n : ℕ) (g : G), (a' n g).hom ≫ xb' n = xb' n) ∧
      (∀ (n : ℕ) (g : G), (a' n g).hom ≫ xt' n = xt' n ≫ (a' (n + 1) g).hom) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_tower_baseChange_of_isPullback.solution
