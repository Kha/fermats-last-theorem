import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_kaehlerDifferential_cover_of_smooth

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ Spec (.of R)) [Smooth c] :
    Module.Flat R Ω[(𝒱.cover c).A0⁄R] ∧ Module.Flat R Ω[(𝒱.cover c).A1⁄R] ∧
      Module.Flat R Ω[(𝒱.cover c).A01⁄R] := by

  have key : ∀ (V : X.Opens) (_ : IsAffineOpen V),
      letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
      Module.Flat R Ω[Γ(X, V)⁄R] := by
    intro V hV
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
    have hs := AlgebraicGeometry.Smooth.smooth_appLE (f := c)
      (AlgebraicGeometry.isAffineOpen_top (Spec (.of R))) hV le_top
    have h1 : ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ V le_top).hom.FormallySmooth := by
      rw [CommRingCat.hom_comp]
      exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).mpr hs.formallySmooth
    have h2 : ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ V le_top).hom.Flat := by
      rw [CommRingCat.hom_comp]
      exact (RingHom.Flat.respectsIso.cancel_left_isIso _ _).mpr hs.flat
    haveI : Algebra.FormallySmooth R Γ(X, V) := h1.toAlgebra
    haveI : Module.Flat R Γ(X, V) := h2
    exact Module.Flat.trans R Γ(X, V) Ω[Γ(X, V)⁄R]
  exact ⟨key 𝒱.U0 𝒱.isAffineOpen_U0, key 𝒱.U1 𝒱.isAffineOpen_U1, key _ 𝒱.isAffineOpen_inf⟩
