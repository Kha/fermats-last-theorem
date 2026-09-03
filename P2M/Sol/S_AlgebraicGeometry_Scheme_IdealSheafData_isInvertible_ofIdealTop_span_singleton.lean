import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_ofIdealTop_span_singleton

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X : Scheme.{u}} [IsAffine X] (r : Γ(X, ⊤)) (hr : r ∈ nonZeroDivisors Γ(X, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop (Ideal.span {r})).IsInvertible := by
  intro x
  let T : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have hle : (X.affineBasicOpen (1 : Γ(X, T)) : X.Opens) ≤ (T : X.Opens) := X.basicOpen_le _
  refine ⟨T, 1, by rw [Scheme.basicOpen_one]; trivial, (X.presheaf.map (homOfLE hle).op).hom r, ?_, ?_⟩
  · letI := T.2.isLocalization_basicOpen (1 : Γ(X, T))
    exact IsLocalization.nonZeroDivisors_le_comap (M := .powers (1 : Γ(X, T)))
      (S := Γ(X, X.basicOpen (1 : Γ(X, T)))) hr
  · rw [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span, Set.image_singleton]
