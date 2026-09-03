import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_mem_preimage_le_of_directed_subalgebra
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type v} (S : ι → Subalgebra R A) (hdir : Directed (· ≤ ·) S) (hS : ∀ a : A, ∃ i, a ∈ S i)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (q : ∀ i, pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap R ↥(S i)))))
    (hq₁ : ∀ i, q i ≫ pullback.fst f _ = pullback.fst f _)
    (hq₂ : ∀ i, q i ≫ pullback.snd f _ =
      pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(S i) A)))
    (U : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A)))).Opens)
    (w : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A))))) (hw : w ∈ U) :
    ∃ (i : ι) (W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R ↥(S i))))).Opens),
      w ∈ (q i) ⁻¹ᵁ W ∧ (q i) ⁻¹ᵁ W ≤ U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra.solution
