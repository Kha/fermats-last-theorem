module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental

@[expose] public section

theorem AlgebraicCurve.finiteDimensional_adjoin_of_transcendental {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] {t : F} (ht : Transcendental K t) :
    FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental.solution
