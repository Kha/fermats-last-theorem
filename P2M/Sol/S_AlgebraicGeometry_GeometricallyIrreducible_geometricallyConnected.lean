import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution {X Y : Scheme.{u}} (f : X ⟶ Y)
    [GeometricallyIrreducible f] : GeometricallyConnected f := by
  refine ⟨?_⟩
  have h := GeometricallyIrreducible.geometrically_irreducibleSpace (f := f)
  rw [geometrically_eq_universally] at h ⊢
  refine MorphismProperty.universally_mono ?_ _ h
  intro X' Y' g hg hI hS
  haveI : IrreducibleSpace X' := hg hI hS
  infer_instance

example {X Y : Scheme.{u}} (f : X ⟶ Y) [GeometricallyIntegral f] : GeometricallyConnected f :=
  solution f
