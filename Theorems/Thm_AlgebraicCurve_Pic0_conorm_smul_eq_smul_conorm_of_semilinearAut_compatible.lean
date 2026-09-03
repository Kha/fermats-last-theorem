import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_conorm_smul_eq_smul_conorm_of_semilinearAut_compatible

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.conorm_smul_eq_smul_conorm_of_semilinearAut_compatible
    {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F'] [Algebra F F']
    (ι : Pic0 K F →+ Pic0 K' F')
    (hpin : ∀ (D : Divisor.degZero (K := K) (F := F)) (D' : Divisor.degZero (K := K') (F := F')),
      (∀ (v' : Place K' F') (v : Place K F),
        v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring →
          (D' : Divisor K' F') v' = (D : Divisor K F) v) →
      (∀ v' : Place K' F',
        (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
          (D' : Divisor K' F') v' = 0) →
      ι (Pic0.mk D) = Pic0.mk D')
    (hex : ∀ D : Divisor.degZero (K := K) (F := F), ∃ D' : Divisor.degZero (K := K') (F := F'),
      (∀ (v' : Place K' F') (v : Place K F),
        v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring →
          (D' : Divisor K' F') v' = (D : Divisor K F) v) ∧
      (∀ v' : Place K' F',
        (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
          (D' : Divisor K' F') v' = 0))
    (σ : SemilinearAut K F) (σ' : SemilinearAut K' F')
    (hcompat : ∀ f : F, σ' • algebraMap F F' f = algebraMap F F' (σ • f)) :
    ∀ x : Pic0 K F, ι (σ • x) = σ' • ι x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_conorm_smul_eq_smul_conorm_of_semilinearAut_compatible.solution
