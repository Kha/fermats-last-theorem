import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_Repartitions
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_linearIndependent_riemannRochSpace_forall_arithmeticGalois_smul_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_linearIndependent_riemannRochSpace_forall_arithmeticGalois_smul_eq
    (M : ℕ) [NeZero M] (S : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M))
    (hE : ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull M) σ • E = E)
    [FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace E)] :
    ∃ b : Fin (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E)) → ↥(modularFunctionFieldBar M),
      (∀ i, b i ∈ riemannRochSpace E) ∧ LinearIndependent (AlgebraicClosure ℚ) b ∧
      ∀ i, ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull M) σ • b i = b i := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_linearIndependent_riemannRochSpace_forall_arithmeticGalois_smul_eq.solution
