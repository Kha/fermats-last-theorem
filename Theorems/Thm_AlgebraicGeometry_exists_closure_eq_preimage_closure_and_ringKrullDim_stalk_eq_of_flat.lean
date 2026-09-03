import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat
    {k : Type u} [Field k] {G P : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    (p : P ⟶ Spec (CommRingCat.of k))
    [GeometricallyIrreducible f] [LocallyOfFiniteType f] [LocallyOfFiniteType p] (w : P) :
    ∃ ζ : ↥(pullback f p),
      closure ({ζ} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure ({w} : Set P) ∧
      (pullback.snd f p).base ζ = w ∧
      ringKrullDim ((pullback f p).presheaf.stalk ζ) = ringKrullDim (P.presheaf.stalk w) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat.solution
