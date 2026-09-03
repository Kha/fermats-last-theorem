import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_coeffCocycles_eq_sum_smul_map_intCast_add_three_of_exists_prime_dvd_mod_three_eq_two
attribute [-simp] ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_coeffCocycles_eq_sum_smul_map_intCast_add_three_of_exists_prime_dvd_mod_three_eq_two
    (F : Type) [Field F] [CharP F 3] (n N : ℕ) [NeZero N] (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ q % 3 = 2)
    (z : ↥(HeckeEis.coeffCocycles
      ((HeckeEis.binaryFormRepSL F n).comp (CongruenceSubgroup.Gamma0 N).subtype))) :
    ∃ (m : ℕ) (c : Fin m → F)
      (y : Fin m → ↥(HeckeEis.coeffCocycles
        ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)))
      (w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm F n)),
      w ∈ HeckeEis.coeffCoboundaries
          ((HeckeEis.binaryFormRepSL F n).comp (CongruenceSubgroup.Gamma0 N).subtype) ∧
        ∀ g : CongruenceSubgroup.Gamma0 N,
          (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm F n)) g : MvPolynomial (Fin 2) F)) =
            (∑ i : Fin m, c i • MvPolynomial.map (Int.castRingHom F)
                (((y i : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℤ n)) g :
                  MvPolynomial (Fin 2) ℤ))) +
              ((w g : ↥(HeckeEis.BinaryForm F n)) : MvPolynomial (Fin 2) F) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_coeffCocycles_eq_sum_smul_map_intCast_add_three_of_exists_prime_dvd_mod_three_eq_two.solution
