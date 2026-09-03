import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_formallyUnramified_of_forall_lift_unique_of_isArtinianRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

theorem AlgebraicGeometry.formallyUnramified_of_forall_lift_unique_of_isArtinianRing
    {R : Type u} [CommRing R] {M : Scheme.{u}} (ϖ : M ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType ϖ]
    (h : ∀ (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
      [CommRing T] [Nontrivial T] (p : T' →+* T), Function.Surjective p → RingHom.ker p * maximalIdeal T' = ⊥ →
      ∀ (s : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of R)) (m : Spec (CommRingCat.of T) ⟶ M),
        m ≫ ϖ = Spec.map (CommRingCat.ofHom p) ≫ s →
        ∀ m₁ m₂ : Spec (CommRingCat.of T') ⟶ M, m₁ ≫ ϖ = s → Spec.map (CommRingCat.ofHom p) ≫ m₁ = m →
          m₂ ≫ ϖ = s → Spec.map (CommRingCat.ofHom p) ≫ m₂ = m → m₁ = m₂) :
    FormallyUnramified ϖ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_formallyUnramified_of_forall_lift_unique_of_isArtinianRing.solution
