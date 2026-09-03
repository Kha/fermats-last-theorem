import Mathlib
import Theorems.Thm_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Etale_isDomain_and_isIntegrallyClosed_stalk

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution {U S : Scheme.{u}} (f : U ⟶ S) [Etale f]
    [IsAffine S] [IsDomain Γ(S, ⊤)] [IsIntegrallyClosed Γ(S, ⊤)] (y : U) :
    IsDomain (U.presheaf.stalk y) ∧ IsIntegrallyClosed (U.presheaf.stalk y) := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    U.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hle : W ≤ f ⁻¹ᵁ ⊤ := le_top
  have hφ : RingHom.Etale (f.appLE ⊤ W hle).hom :=
    HasRingHomProperty.appLE @Etale f inferInstance ⟨⊤, isAffineOpen_top S⟩ ⟨W, hW⟩ hle
  letI := (f.appLE ⊤ W hle).hom.toAlgebra
  haveI : Algebra.Etale Γ(S, ⊤) Γ(U, W) := hφ
  letI := TopCat.Presheaf.algebra_section_stalk U.presheaf (⟨y, hyW⟩ : W)
  haveI := hW.isLocalization_stalk ⟨y, hyW⟩
  exact Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime Γ(S, ⊤) Γ(U, W)
    (hW.primeIdealOf ⟨y, hyW⟩).asIdeal (U.presheaf.stalk y)
