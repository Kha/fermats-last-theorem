import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_locallyOfFinitePresentation_of_forall_directed_colimit
attribute [-instance] IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty
attribute [-simp] IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.locallyOfFinitePresentation_of_forall_directed_colimit
    {𝒪 : Type u} [CommRing 𝒪] {M : Scheme.{u}} (πM : M ⟶ Spec (CommRingCat.of 𝒪))
    (H : ∀ (ι : Type u) [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
      (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra 𝒪 (S i)]
      (t : ∀ i j, i ≤ j → (S i →ₐ[𝒪] S j))
      (_ : ∀ i (h : i ≤ i), t i i h = AlgHom.id 𝒪 (S i))
      (_ : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (t j k hjk).comp (t i j hij) = t i k (hij.trans hjk))
      (L : Type u) [CommRing L] [Algebra 𝒪 L] (c : ∀ i, S i →ₐ[𝒪] L)
      (_ : ∀ i j (h : i ≤ j), (c j).comp (t i j h) = c i)
      (_ : ∀ x : L, ∃ (i : ι) (y : S i), c i y = x)
      (_ : ∀ (i : ι) (y z : S i), c i y = c i z → ∃ (j : ι) (h : i ≤ j), t i j h y = t i j h z),
      (∀ x : Spec (CommRingCat.of L) ⟶ M, x ≫ πM = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 L)) →
          ∃ (i : ι) (xi : Spec (CommRingCat.of (S i)) ⟶ M), xi ≫ πM = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (S i))) ∧
            x = Spec.map (CommRingCat.ofHom (c i).toRingHom) ≫ xi) ∧
      (∀ (i : ι) (xi yi : Spec (CommRingCat.of (S i)) ⟶ M),
          xi ≫ πM = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (S i))) → yi ≫ πM = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (S i))) →
          Spec.map (CommRingCat.ofHom (c i).toRingHom) ≫ xi = Spec.map (CommRingCat.ofHom (c i).toRingHom) ≫ yi →
          ∃ (j : ι) (h : i ≤ j), Spec.map (CommRingCat.ofHom (t i j h).toRingHom) ≫ xi = Spec.map (CommRingCat.ofHom (t i j h).toRingHom) ≫ yi)) :
    LocallyOfFinitePresentation πM := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_locallyOfFinitePresentation_of_forall_directed_colimit.solution
