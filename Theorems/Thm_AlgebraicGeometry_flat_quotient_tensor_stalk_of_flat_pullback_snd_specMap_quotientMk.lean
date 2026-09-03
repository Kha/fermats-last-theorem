import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_flat_quotient_tensor_stalk_of_flat_pullback_snd_specMap_quotientMk

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.flat_quotient_tensor_stalk_of_flat_pullback_snd_specMap_quotientMk
    {R : Type u} [CommRing R] (J : Ideal R) {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of R))
    [Flat (pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))] (z : ↥Z) :
    letI : Algebra R ↑(Z.presheaf.stalk z) :=
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ Z.presheaf.germ ⊤ z trivial).hom).toAlgebra
    Module.Flat (R ⧸ J) ((R ⧸ J) ⊗[R] ↑(Z.presheaf.stalk z)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_flat_quotient_tensor_stalk_of_flat_pullback_snd_specMap_quotientMk.solution
