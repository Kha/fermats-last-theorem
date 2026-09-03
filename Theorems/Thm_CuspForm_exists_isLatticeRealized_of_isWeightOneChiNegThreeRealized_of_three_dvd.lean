import Mathlib
import Definitions.Def_LanglandsTunnell_WeightOneRealizationCarriers
import P2M.Util
import P2M.Sol.S_CuspForm_exists_isLatticeRealized_of_isWeightOneChiNegThreeRealized_of_three_dvd
attribute [-instance] Ihara.instGroupIharaAmalgam
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway

set_option autoImplicit false

open FLT.ExplicitLift EisensteinWeightOne CuspForm

theorem CuspForm.exists_isLatticeRealized_of_isWeightOneChiNegThreeRealized_of_three_dvd
    (M : ℕ) [NeZero M] (h3 : 3 ∣ M) (b : ℕ → ℤ√(-2))
    (heig : FormalHecke.IsEigensystem
      (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ√(-2))) b)
    (hbasis : CuspForm.HasIntegralBasis M)
    (hreal : CuspForm.IsWeightOneChiNegThreeRealized M b) :
    ∃ a : ℕ → ℤ,
      FormalHecke.IsEigensystem (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ)) a ∧
      CuspForm.IsLatticeRealized M a ∧
      ∀ n : ℕ, ((a n : ℤ) : ZMod 3) = red (b n) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_isLatticeRealized_of_isWeightOneChiNegThreeRealized_of_three_dvd.solution
