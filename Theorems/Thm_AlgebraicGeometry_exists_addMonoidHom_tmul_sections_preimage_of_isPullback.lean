import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_addMonoidHom_tmul_sections_preimage_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TensorProduct

theorem AlgebraicGeometry.exists_addMonoidHom_tmul_sections_preimage_of_isPullback
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (Y : ℕ → Scheme.{0}) (yb : ∀ n : ℕ, Y n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (yt : ∀ n : ℕ, Y n ⟶ Y (n + 1))
    (S : Type) [CommRing S] [Algebra 𝒪 S]
    (Y' : ℕ → Scheme.{0})
    (yb' : ∀ n : ℕ, Y' n ⟶ Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})))
    (yt' : ∀ n : ℕ, Y' n ⟶ Y' (n + 1)) (r : ∀ n : ℕ, Y' n ⟶ Y n)
    (hbase : ∀ n : ℕ, IsPullback (r n) (yb' n) (yb n)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))))
    (hyt'r : ∀ n : ℕ, yt' n ≫ r (n + 1) = r n ≫ yt n)
    (hyt'b : ∀ n : ℕ, yt' n ≫ yb' (n + 1) = yb' n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 S π) (Nat.le_succ (n + 1)))))))
    (V : ∀ n : ℕ, (Y n).Opens) (hVa : ∀ n : ℕ, IsAffineOpen (V n))
    (hV : ∀ n : ℕ, (yt n) ⁻¹ᵁ (V (n + 1)) = V n)
    (A : Type) [CommRing A] [Algebra 𝒪 A]
    (μ : ∀ n : ℕ, (A ⧸ Ideal.span {algebraMap 𝒪 A π ^ (n + 1)}) ≃+* Γ(Y n, V n))
    (hμ_yt : ∀ (n : ℕ) (x : A), (yt n).appLE (V (n + 1)) (V n) (by rw [hV])
        (μ (n + 1) (Ideal.Quotient.mk _ x)) = μ n (Ideal.Quotient.mk _ x))
    (hμ_yb : ∀ (n : ℕ) (o : 𝒪), μ n (Ideal.Quotient.mk _ (algebraMap 𝒪 A o)) =
        (yb n).appLE ⊤ (V n) le_top
          ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))) :
    ∃ (φ : ∀ n : ℕ, (A ⊗[𝒪] S) →+ Γ(Y' n, (r n) ⁻¹ᵁ (V n))),
      (∀ (n : ℕ) (x : A) (s : S), φ n (x ⊗ₜ[𝒪] s) =
          (r n).appLE (V n) ((r n) ⁻¹ᵁ (V n)) le_rfl (μ n (Ideal.Quotient.mk _ x)) *
          (yb' n).appLE ⊤ ((r n) ⁻¹ᵁ (V n)) le_top
            ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s))) ∧
      (∀ n : ℕ, Function.Surjective (φ n)) ∧
      (∀ (b : A ⊗[𝒪] S) (n : ℕ), (yt' n) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b)) = (Y' n).basicOpen (φ n b)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_addMonoidHom_tmul_sections_preimage_of_isPullback.solution
