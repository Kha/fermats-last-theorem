import Definitions.Def_ModularCurve_X0ModL
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve

theorem ModularCurve.exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd (K : Type*) [Field K]
    (N p : ℕ) [NeZero N] [NeZero p] (hp : p.Prime) (hpN : ¬ p ∣ N) (hNK : (N : K) ≠ 0) (hpK : (p : K) ≠ 0) :
    ∃ σ : modularFunctionFieldFullC K (N * p) ≃ₐ[K] modularFunctionFieldFullC K (N * p),
      ∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ N),
        σ ⟨qExpand K d (jqModC K), jqModCd_mem_full K (N * p) (Dvd.dvd.mul_right hd p)⟩
            = ⟨qExpand K (d * p) (jqModC K), jqModCd_mem_full K (N * p) (Nat.mul_dvd_mul_right hd p)⟩
          ∧ σ ⟨qExpand K (d * p) (jqModC K), jqModCd_mem_full K (N * p) (Nat.mul_dvd_mul_right hd p)⟩
            = ⟨qExpand K d (jqModC K), jqModCd_mem_full K (N * p) (Dvd.dvd.mul_right hd p)⟩ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd.solution
