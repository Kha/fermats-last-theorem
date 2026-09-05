module

public import Mathlib
public import Definitions.Def_ModularCurve_ArithmeticGalois
public import Definitions.Def_ModularCurve_CuspidalClass
public import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
public import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_exists_transcendental_finiteDimensional_modularFunctionFieldBar

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem solution (N : ℕ) [NeZero N] :
    ∃ x : modularFunctionFieldBar N, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (modularFunctionFieldBar N)))
        (modularFunctionFieldBar N) :=
  ⟨_, ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N,
    ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_of_neZero N⟩
