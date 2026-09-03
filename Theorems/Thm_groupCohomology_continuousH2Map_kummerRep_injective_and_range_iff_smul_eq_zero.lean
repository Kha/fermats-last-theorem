import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
import P2M.Sol.S_groupCohomology_continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero

set_option autoImplicit false
open CategoryTheory

open groupCohomology IntermediateField
theorem groupCohomology.continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K Ω, FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup) :
    let j : continuousH2 r (Kummer.kummerRep K Ω p) →ₗ[ℤ] continuousH2 r (Rep.ofAlgebraAutOnUnits K Ω) :=
      continuousH2Map (rH := r) (rG := r) (A := Kummer.kummerRep K Ω p) (B := Rep.ofAlgebraAutOnUnits K Ω)
        (MonoidHom.id _) (fun _ => rfl)
        (MonoidHom.toAdditive (rootsOfUnity p Ω).subtype).toIntLinearMap (fun _ _ => rfl)
    Function.Injective j ∧
      ∀ x : continuousH2 r (Rep.ofAlgebraAutOnUnits K Ω), x ∈ LinearMap.range j ↔ (p : ℤ) • x = 0 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero.solution
