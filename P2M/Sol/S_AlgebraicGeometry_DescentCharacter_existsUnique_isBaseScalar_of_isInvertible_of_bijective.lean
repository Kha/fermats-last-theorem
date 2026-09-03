import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_DescentCharacter_existsUnique_isBaseScalar_of_isInvertible_of_bijective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry AlgebraicGeometry.DescentCharacter

theorem solution
    {X : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    (hH0 : Function.Bijective fun c : R => f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))
    {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (σ : M ⟶ M) :
    ∃! c : R, IsBaseScalar f σ c := by
  obtain ⟨s, hs, huniq⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_app_eq_smul hM σ
  obtain ⟨c, hc⟩ := hH0.2 s
  simp only at hc
  refine ⟨c, ?_, ?_⟩
  · intro U x
    rw [hs U x]
    show _ = X.presheaf.map (homOfLE (le_top (a := U))).op
      (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c)) • x
    rw [hc]
  · intro c' hc'
    have h1 : f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c') = s :=
      huniq (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c')) (fun U x => hc' U x)
    apply hH0.1
    show f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c') =
      f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c)
    rw [h1]
    exact hc.symm
