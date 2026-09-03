import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_Deformations_MatrixRepresentation
import Definitions.Def_LanglandsTunnell_ExplicitLift
import Definitions.Def_GaloisRep_ModThreeCyclotomic
import Definitions.Def_ModularForm_EisensteinChiNegThree
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_det_map_comp_lift_eq_chiNegThree_of_isFrobeniusAt

set_option autoImplicit false

open WeierstrassCurve FLT.ExplicitLift EisensteinWeightOne

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem LanglandsTunnell.det_map_comp_lift_eq_chiNegThree_of_isFrobeniusAt
    (ρ : Γℚ →* GL (Fin 2) (ZMod 3))
    (hdet : ∀ σ : Γℚ, Matrix.GeneralLinearGroup.det (ρ σ) = modThreeCyclotomicChar σ)
    (Ψ : GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ℤ√(-2)))
    (hΨ : ∀ g, Matrix.GeneralLinearGroup.map red (Ψ g) = g) (ι : ℤ√(-2) →+* ℂ)
    (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (σ : Γℚ) (hσ : A.IsFrobeniusAt σ p) :
    (((Matrix.GeneralLinearGroup.map (n := Fin 2) ι).comp (Ψ.comp ρ) σ : GL (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ).det = ((chiNegThree p : ℤ) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_det_map_comp_lift_eq_chiNegThree_of_isFrobeniusAt.solution
