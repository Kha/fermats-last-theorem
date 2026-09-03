import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_eq_prime_smul_of_coeffH1par_map_eq_zero (N : ℕ) [NeZero N] (n : ℕ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpN : ¬ p ∣ N) (hn : n < p)
    (K : Type*) [Field K] [CharP K p]
    (Φ : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hΦ : (∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)), ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (∀ g : CongruenceSubgroup.Gamma0 N, ((w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) g : MvPolynomial (Fin 2) K)
            = MvPolynomial.map (Int.castRingHom K) (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℤ n)) g : MvPolynomial (Fin 2) ℤ))) ∧
        Φ (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w))
    (y : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)) (hy : Φ y = 0) :
    ∃ y' : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype), y = (p : ℤ) • y' := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.solution
