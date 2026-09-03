import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_forall_sections_eq_univ
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_sigma_eq_smul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PUtoProj

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {M : X.Modules} {f : X ⟶ Spec (CommRingCat.of R)} {N : ℕ}

noncomputable def rescale (P : Scheme.Modules.ProjPresentation M f N) (c : Γ(X, ⊤)) (hc : IsUnit c) :
    Scheme.Modules.ProjPresentation M f N where
  σ i := c • P.σ i
  toProj := P.toProj
  toProj_π := P.toProj_π
  frame i V hV := by
    have hcV : IsUnit (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op c) := hc.map _
    have key : (fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (c • P.σ i) : Γ(M, V))) =
        (fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (P.σ i) : Γ(M, V))) ∘
          (fun g : Γ(X, V) => g * X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op c) := by
      funext g
      simp only [Function.comp_apply, Scheme.Modules.map_smul, smul_smul]
    obtain ⟨u, hu⟩ := hcV
    rw [key, ← hu]
    exact (P.frame i V hV).comp (Units.mulRight u).bijective
  app_ratio_smul i j := by
    rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul, smul_comm, P.app_ratio_smul i j]

end PUtoProj

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {M : X.Modules} {f : X ⟶ Spec (CommRingCat.of R)} {N : ℕ}
    (P P' : M.ProjPresentation f N) (c : Γ(X, ⊤)) (hc : IsUnit c)
    (h : ∀ i : Fin (N + 1), P'.σ i = c • P.σ i) :
    P'.toProj = P.toProj := by
  have e := AlgebraicGeometry.Scheme.Modules.ProjPresentation.toProj_eq_of_forall_sections_eq_univ P'
    (PUtoProj.rescale P c hc) (fun i => h i)
  exact e
