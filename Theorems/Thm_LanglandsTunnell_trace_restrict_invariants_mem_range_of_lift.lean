import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_Deformations_MatrixRepresentation
import Definitions.Def_LanglandsTunnell_ExplicitLift
import Definitions.Def_GaloisRep_ModThreeCyclotomic
import Definitions.Def_ModularForm_EisensteinChiNegThree
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_trace_restrict_invariants_mem_range_of_lift

set_option autoImplicit false

open WeierstrassCurve FLT.ExplicitLift EisensteinWeightOne

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem LanglandsTunnell.trace_restrict_invariants_mem_range_of_lift
    (ρ : Γℚ →* GL (Fin 2) (ZMod 3))
    (Ψ : GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ℤ√(-2)))
    (hΨ : ∀ g, Matrix.GeneralLinearGroup.map red (Ψ g) = g) (ι : ℤ√(-2) →+* ℂ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : Γℚ) (hσ : A.IsFrobeniusAt σ ℓ)
    (hpres : ∀ v ∈ Representation.invariants
        ((Deformation.matrixRepresentation
            ((Matrix.GeneralLinearGroup.map (n := Fin 2) ι).comp (Ψ.comp ρ))).comp
          (A.inertiaSubgroupIn ℚ).subtype),
      Deformation.matrixRepresentation
          ((Matrix.GeneralLinearGroup.map (n := Fin 2) ι).comp (Ψ.comp ρ)) σ v ∈
        Representation.invariants
          ((Deformation.matrixRepresentation
              ((Matrix.GeneralLinearGroup.map (n := Fin 2) ι).comp (Ψ.comp ρ))).comp
            (A.inertiaSubgroupIn ℚ).subtype)) :
    LinearMap.trace ℂ _
        ((Deformation.matrixRepresentation
            ((Matrix.GeneralLinearGroup.map (n := Fin 2) ι).comp (Ψ.comp ρ)) σ).restrict hpres) ∈
      Set.range (ι : ℤ√(-2) → ℂ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_trace_restrict_invariants_mem_range_of_lift.solution
