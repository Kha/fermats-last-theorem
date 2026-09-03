import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_linearIndependent_riemannRochSpace_forall_arithmeticGalois_smul_eq_xH

set_option autoImplicit false

open AlgebraicCurve ModularCurve
open scoped MatrixGroups

theorem ModularCurve.exists_linearIndependent_riemannRochSpace_forall_arithmeticGalois_smul_eq_xH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hE : ∀ σ ∈ S, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • E = E)
    [FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace E)] :
    ∃ b : Fin (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E)) → ↥(xHFunctionFieldBar M H),
      (∀ i, b i ∈ riemannRochSpace E) ∧ LinearIndependent (AlgebraicClosure ℚ) b ∧
      ∀ i, ∀ σ ∈ S, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • b i = b i := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_linearIndependent_riemannRochSpace_forall_arithmeticGalois_smul_eq_xH.solution
