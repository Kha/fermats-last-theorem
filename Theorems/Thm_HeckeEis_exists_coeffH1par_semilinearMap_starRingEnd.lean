import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_coeffH1par_semilinearMap_starRingEnd

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_coeffH1par_semilinearMap_starRingEnd (n : ℕ) (Γ : Subgroup SL(2, ℤ)) :
    ∃ Φ : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype) →ₛₗ[starRingEnd ℂ] HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype),
      (∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype)),
        ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype)),
          (∀ g : Γ, ((w : Γ → ↥(HeckeEis.BinaryForm ℂ n)) g : MvPolynomial (Fin 2) ℂ)
              = MvPolynomial.map (starRingEnd ℂ)
                  (((z : Γ → ↥(HeckeEis.BinaryForm ℂ n)) g : MvPolynomial (Fin 2) ℂ))) ∧
          Φ (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w) ∧
      ∀ x : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype), Φ (Φ x) = x := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_coeffH1par_semilinearMap_starRingEnd.solution
