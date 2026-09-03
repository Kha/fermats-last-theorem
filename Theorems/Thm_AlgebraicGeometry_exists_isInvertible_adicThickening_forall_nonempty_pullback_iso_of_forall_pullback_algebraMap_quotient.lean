import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_AdicThickening
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isInvertible_adicThickening_forall_nonempty_pullback_iso_of_forall_pullback_algebraMap_quotient

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isInvertible_adicThickening_forall_nonempty_pullback_iso_of_forall_pullback_algebraMap_quotient
    {S R : Type u} [CommRing S] [CommRing R] [Algebra S R] (I : Ideal R)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of S))

    (j : ∀ k : ℕ, pullback g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1))))) ⟶
      pullback g (Spec.map (CommRingCat.ofHom (algebraMap S R))))
    (hj₁ : ∀ k, j k ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap S R))) =
      pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1))))))
    (hj₂ : ∀ k, j k ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S R))) =
      pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1))))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (k + 1)))))
    (t : ∀ k : ℕ, pullback g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1))))) ⟶
      pullback g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1 + 1))))))
    (ht₁ : ∀ k, t k ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1 + 1))))) =
      pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1))))))
    (ht : ∀ k, t k ≫ j (k + 1) = j k)

    (𝓛k : ∀ k : ℕ, (pullback g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1)))))).Modules)
    (hinv : ∀ k, Scheme.Modules.IsInvertible (𝓛k k))
    (hcompat : ∀ k : ℕ, Nonempty ((Scheme.Modules.pullback (t k)).obj (𝓛k (k + 1)) ≅ 𝓛k k)) :
    ∃ L : ∀ n : ℕ, (adicThickening (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S R)))) I n).Modules,
      (∀ n, Scheme.Modules.IsInvertible (L n)) ∧
      (∀ n, Nonempty ((Scheme.Modules.pullback
        (adicThickeningTransition (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S R)))) I n)).obj
          (L (n + 1)) ≅ L n)) ∧
      ∀ M : (pullback g (Spec.map (CommRingCat.ofHom (algebraMap S R)))).Modules,
        (∀ n, Nonempty ((Scheme.Modules.pullback
          (adicThickeningι (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S R)))) I n)).obj M ≅ L n)) →
        ∀ k : ℕ, Nonempty ((Scheme.Modules.pullback (j k)).obj M ≅ 𝓛k k) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isInvertible_adicThickening_forall_nonempty_pullback_iso_of_forall_pullback_algebraMap_quotient.solution
