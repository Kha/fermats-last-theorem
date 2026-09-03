import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Basic
import P2M.Util
import P2M.Sol.S_CuspFormClass_isZeroAt_slash_slash_heckeDiagMatrix_of_mem_Gamma0

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspFormClass.isZeroAt_slash_slash_heckeDiagMatrix_of_mem_Gamma0
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (ℓ : ℕ) [NeZero ℓ]
    (σ : CongruenceSubgroup.Gamma0 M)
    {F : Type*} [FunLike F UpperHalfPlane ℂ]
    [CuspFormClass F (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    {c : OnePoint ℝ} (hc : IsCusp c (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ))) :
    OnePoint.IsZeroAt c
      ((⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ))) ∣[k]
        ModularForm.heckeDiagMatrix ℓ) k := by p2m_exact_reverting @_root_.P2MW.S_CuspFormClass_isZeroAt_slash_slash_heckeDiagMatrix_of_mem_Gamma0.solution
