import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Theorems.Thm_Algebra_exists_isDirectLimit_of_finitePresentation
import P2M.Util
namespace P2MW.S_Algebra_FinitePresentation_of_forall_isDirectLimit_exists_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (H : ∀ (ι : Type u) [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
      (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
      (t : ∀ i j : ι, i ≤ j → (S i →ₐ[R] S j)) [DirectedSystem S fun i j h => ⇑(t i j h)]
      (L : Type u) [CommRing L] [Algebra R L] (c : ∀ i, S i →ₐ[R] L)
      [IsDirectLimit (fun i j h => ⇑(t i j h)) fun i => ⇑(c i)]
      (ψ : A →ₐ[R] L), ∃ (i : ι) (φ : A →ₐ[R] S i), (c i).comp φ = ψ) :
    Algebra.FinitePresentation R A := by
  classical
  obtain ⟨ι, _, _, _, S, _, _, hfp, t, c, hds, hlim⟩ := Algebra.exists_isDirectLimit_of_finitePresentation R A
  obtain ⟨i, φ, hφ⟩ := H ι S t A c (AlgHom.id R A)

  have hsec : ∀ a : A, c i (φ a) = a := fun a => by
    have := congrArg (fun f : A →ₐ[R] A => f a) hφ
    simpa using this
  have hsurj : Function.Surjective (c i) := fun a => ⟨φ a, hsec a⟩
  haveI : Algebra.FinitePresentation R (S i) := hfp i

  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R (S i)).out

  set σ : S i →ₐ[R] S i := φ.comp (c i) with hσ
  set I : Ideal (S i) := Ideal.span ((fun x => x - σ x) '' (s : Set (S i))) with hI
  have hIker : I = RingHom.ker (c i).toRingHom := by
    apply le_antisymm
    · rw [hI, Ideal.span_le]
      rintro _ ⟨x, _, rfl⟩
      simp [RingHom.mem_ker, hσ, hsec]
    · intro y hy
      rw [RingHom.mem_ker] at hy

      have key : ∀ y : S i, y - σ y ∈ I := by
        let T : Subalgebra R (S i) :=
          { carrier := {y | y - σ y ∈ I}
            mul_mem' := by
              intro a b ha hb
              simp only [Set.mem_setOf_eq] at ha hb ⊢
              have : a * b - σ (a * b) = a * (b - σ b) + (a - σ a) * σ b := by
                rw [map_mul]; ring
              rw [this]
              exact I.add_mem (I.mul_mem_left _ hb) (I.mul_mem_right _ ha)
            add_mem' := by
              intro a b ha hb
              simp only [Set.mem_setOf_eq] at ha hb ⊢
              have : a + b - σ (a + b) = (a - σ a) + (b - σ b) := by rw [map_add]; ring
              rw [this]
              exact I.add_mem ha hb
            algebraMap_mem' := by
              intro r
              simp only [Set.mem_setOf_eq, AlgHom.commutes, sub_self]
              exact I.zero_mem }
        have hsT : (s : Set (S i)) ⊆ T := fun x hx => Ideal.subset_span ⟨x, hx, rfl⟩
        have hT : (⊤ : Subalgebra R (S i)) ≤ T := by
          rw [← hs]
          exact Algebra.adjoin_le hsT
        intro y
        exact hT (Algebra.mem_top : y ∈ (⊤ : Subalgebra R (S i)))
      have : y = y - σ y := by
        simp only [hσ, AlgHom.comp_apply]
        rw [show (c i) y = 0 from hy, map_zero, sub_zero]
      rw [this]
      exact key y
  have hker : (RingHom.ker (c i).toRingHom).FG := ⟨(s.image fun x => x - σ x), by rw [Finset.coe_image, ← hI, hIker]⟩
  exact Algebra.FinitePresentation.of_surjective hsurj hker
