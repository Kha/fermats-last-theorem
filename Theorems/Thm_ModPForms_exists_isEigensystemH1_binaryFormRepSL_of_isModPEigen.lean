import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen
import P2M.Util
import P2M.Sol.S_ModPForms_exists_isEigensystemH1_binaryFormRepSL_of_isModPEigen
attribute [-simp] HeckeEis.coe_linePow ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply

set_option autoImplicit false

open scoped MatrixGroups

theorem ModPForms.exists_isEigensystemH1_binaryFormRepSL_of_isModPEigen (p : ℕ) (hp : p.Prime)
    (N' : ℕ) [NeZero N'] (hpN' : ¬ p ∣ N')
    (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (hS₀p : p ∈ S₀) (F : Type) [Field F] [CharP F p]
    (k : ℤ) (hk : 2 ≤ k) (φ : PowerSeries F) (lam : ℕ → F)
    (hφ : φ ∈ ModPForms.modPMod N' k F) (heig : ModPForms.IsModPEigen N' S₀ k φ lam) :
    ∃ j : ℕ, HeckeEis.IsEigensystemH1 N'
      ((HeckeEis.binaryFormRepSL F (k - 2).toNat).comp (CongruenceSubgroup.Gamma0 N').subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj F (k - 2).toNat ℓ) S₀ (fun ℓ => (ℓ : F) ^ j * lam ℓ) := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_exists_isEigensystemH1_binaryFormRepSL_of_isModPEigen.solution
