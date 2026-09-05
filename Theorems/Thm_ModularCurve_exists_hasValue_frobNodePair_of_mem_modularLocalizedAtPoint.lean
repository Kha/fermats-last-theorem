module

public import Mathlib
public import Definitions.Def_ModularCurve_NodeLocalized
public import Definitions.Def_AlgebraicCurve_GluedPic0
public import Definitions.Def_ModularCurve_SupersingularNodes
public import Definitions.Def_ModularCurve_SupersingularModuli
public import Definitions.Def_ModularCurve_CuspidalClass
public import Definitions.Def_ModularCurve_ArithmeticGalois
public import P2M.Util
public import P2M.Sol.S_ModularCurve_exists_hasValue_frobNodePair_of_mem_modularLocalizedAtPoint

@[expose] public section
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve
theorem ModularCurve.exists_hasValue_frobNodePair_of_mem_modularLocalizedAtPoint
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha2 : a ^ (q ^ 2) = a)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.modularLocalizedAtPoint (1 * q) A.toSubring red a (a ^ q)) :
    ∃ (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
      (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1)
      (h₂ : ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
              ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
      (h₂F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ∈ modularFunctionFieldC k 1)
      (c : k),
      (frobNodePair q a).1.HasValue (⟨_, h₁F⟩ : modularFunctionFieldC k 1) c ∧
      (frobNodePair q a).2.HasValue (⟨_, h₂F⟩ : modularFunctionFieldC k 1) c := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_mem_modularLocalizedAtPoint.solution
