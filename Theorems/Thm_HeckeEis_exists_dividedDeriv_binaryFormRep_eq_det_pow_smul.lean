import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_dividedDeriv_binaryFormRep_eq_det_pow_smul

set_option autoImplicit false

open MvPolynomial in

theorem HeckeEis.exists_dividedDeriv_binaryFormRep_eq_det_pow_smul (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [CharP K p] (a : ℕ) :
    ∃ D : ↥(HeckeEis.BinaryForm K (a + (p - 1))) →ₗ[K] ↥(HeckeEis.BinaryForm K (p - 1 - a)),
      (∀ F : ↥(HeckeEis.BinaryForm K (a + (p - 1))),
        ((D F : ↥(HeckeEis.BinaryForm K (p - 1 - a))) : MvPolynomial (Fin 2) K)
          = ∑ k ∈ Finset.Ico a p,
              monomial (Finsupp.single 0 (k - a) + Finsupp.single 1 (p - 1 - k))
                (coeff (Finsupp.single 0 k + Finsupp.single 1 (a + (p - 1) - k))
                  (F : MvPolynomial (Fin 2) K) * (k.descFactorial a : K))) ∧
      (∀ F : ↥(HeckeEis.BinaryForm K (a + (p - 1))),
        (X 1 : MvPolynomial (Fin 2) K) ^ a
            * ((D F : ↥(HeckeEis.BinaryForm K (p - 1 - a))) : MvPolynomial (Fin 2) K)
          = (fun G : MvPolynomial (Fin 2) K => pderiv 0 G)^[a] (F : MvPolynomial (Fin 2) K)) ∧
      (∀ (M : Matrix (Fin 2) (Fin 2) ℤ) (F : ↥(HeckeEis.BinaryForm K (a + (p - 1)))),
        D (HeckeEis.binaryFormRep K (a + (p - 1)) M F)
          = (((M.det : ℤ) : K) ^ a) • HeckeEis.binaryFormRep K (p - 1 - a) M (D F)) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_dividedDeriv_binaryFormRep_eq_det_pow_smul.solution
