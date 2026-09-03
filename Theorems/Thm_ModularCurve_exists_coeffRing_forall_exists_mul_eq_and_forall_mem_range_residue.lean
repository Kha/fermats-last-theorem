import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_coeffRing_forall_exists_mul_eq_and_forall_mem_range_residue

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
  ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.exists_coeffRing_forall_exists_mul_eq_and_forall_mem_range_residue
    (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (S : Finset (AlgebraicClosure ℚ)) (k₀ : Subfield (ResidueField ↥A)) [Finite ↥k₀] :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (ρO' : R p →+* O')
      (ιA' : O' →+* ↥A) (_ : Function.Injective ιA') (_ : IsLocalHom ιA') (_ : ιA'.comp ρO' = ρ)
      (jO' : O' →+* AlgebraicClosure ℚ) (_ : jO'.comp ρO' = algebraMap (R p) (AlgebraicClosure ℚ)) (_ : A.subtype.comp ιA' = jO')
      (_ : ((IsLocalRing.residue ↥A).comp ιA').comp ρO' = (IsLocalRing.residue ↥A).comp ρ),
      (∀ c ∈ S, ∃ a b : O', jO' b ≠ 0 ∧ c * jO' b = jO' a) ∧
      (∀ ξ : ResidueField ↥A, ξ ∈ k₀ → ξ ∈ Set.range ((IsLocalRing.residue ↥A).comp ιA')) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_coeffRing_forall_exists_mul_eq_and_forall_mem_range_residue.solution
