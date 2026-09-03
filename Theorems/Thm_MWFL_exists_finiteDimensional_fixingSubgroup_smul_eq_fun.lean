import Definitions.Def_ModularCurve_ArithmeticGalois
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.FieldTheory.KrullTopology
import P2M.Util
import P2M.Sol.S_MWFL_exists_finiteDimensional_fixingSubgroup_smul_eq_fun

open ModularCurve AlgebraicCurve
theorem MWFL.exists_finiteDimensional_fixingSubgroup_smul_eq_fun (N : ℕ) [NeZero N]
    (z : modularFunctionFieldBar N) :
    ∃ L₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L₀ ∧
      ∀ σ ∈ L₀.fixingSubgroup, arithmeticGalois (modularFunctionFieldFull N) σ • z = z := by p2m_exact_reverting @_root_.P2MW.S_MWFL_exists_finiteDimensional_fixingSubgroup_smul_eq_fun.solution
