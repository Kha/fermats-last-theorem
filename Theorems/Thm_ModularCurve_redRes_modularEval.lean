module

public import Mathlib
public import Definitions.Def_ModularCurve_NodeLocalized
public import P2M.Util
public import P2M.Sol.S_ModularCurve_redRes_modularEval

@[expose] public section

set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized ModularCurve.CharPReduction
theorem ModularCurve.redRes_modularEval (N : ℕ) [NeZero N] {L : Type*} [Field L] (A : Subring L)
    {k : Type*} [Field k] (red : A →+* k) (p : MvPolynomial (Fin 2) A)
    (hp : NodeLocalized.modularEval N A p ∈ CharPReduction.modularRing N A) :
    CharPReduction.redRes A red (CharPReduction.modularRing N A) (CharPReduction.modularRing_le_integralCoeffs N A)
        ⟨NodeLocalized.modularEval N A p, hp⟩
      = MvPolynomial.eval₂Hom ((algebraMap k (LaurentSeries k)).comp red) ![jqModC k, jqNModC k N] p := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_redRes_modularEval.solution
