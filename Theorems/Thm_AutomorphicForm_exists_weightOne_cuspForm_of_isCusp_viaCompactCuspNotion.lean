import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_LanglandsTunnell_RealizationDictionary
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val

open CongruenceSubgroup EisensteinWeightOne
open scoped MatrixGroups ModularForm
theorem AutomorphicForm.exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion
    (Φ : HeckeEigensystem ℚ (ℤ√(-2))) (hΦ : AutomorphicForm.viaCompactCuspNotion.IsCusp ℚ Φ)
    (T : Finset ℕ) :
    ∃ (M : ℕ) (_ : NeZero M), 3 ∣ M ∧ (∀ ℓ ∈ T, ℓ ≠ 0 → ℓ ∣ M) ∧
      ∃ (g : CuspForm (Gamma1 M) 1) (b : ℕ → ℤ√(-2)),
        (∀ γ : SL(2, ℤ), γ ∈ Gamma0 M →
          (⇑g) ∣[(1 : ℤ)] γ = ((chiNegThree (((γ 1 1 : ℤ) : ZMod 3).val) : ℤ) : ℂ) • (⇑g)) ∧
        (∀ n, ModularFormClass.qCoeff (⇑g) n =
          ((b n).re : ℂ) + ((b n).im : ℂ) * ((Real.sqrt 2 : ℂ) * Complex.I)) ∧
        b 0 = 0 ∧
        FormalHecke.IsEigensystem
          (fun ℓ => if ℓ ∣ M then (0 : ℤ√(-2)) else ((chiNegThree ℓ : ℤ) : ℤ√(-2))) b ∧
        ∀ (p : ℕ) (hp : p.Prime), ¬ p ∣ 3 * M → b p = Φ.a (AutomorphicForm.ratPrime ⟨p, hp⟩) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.solution
