module

public import Definitions.Def_ModularCurve_CharPReduction
public import P2M.Util
public import P2M.Sol.S_ModularCurve_CharPReduction_modularRedLocHom_mem

@[expose] public section

open ModularCurve CharPReduction
theorem ModularCurve.CharPReduction.modularRedLocHom_mem {L : Type*} [CommRing L] (A : Subring L)
    {k : Type*} [Field k] (red : A →+* k) (N : ℕ) [NeZero N]
    (f : modularLocalized N A red) :
    modularRedLocHom N A red f ∈ modularFunctionFieldC k N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CharPReduction_modularRedLocHom_mem.solution
