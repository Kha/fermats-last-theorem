module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Algebraic.Defs
public import P2M.Util
public import P2M.Sol.S_KaehlerDifferential_span_D_eq_top_of_transcendental

@[expose] public section

theorem KaehlerDifferential.span_D_eq_top_of_transcendental (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcendental K x)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :
    Submodule.span F ({KaehlerDifferential.D K F x} : Set (KaehlerDifferential K F)) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_KaehlerDifferential_span_D_eq_top_of_transcendental.solution
