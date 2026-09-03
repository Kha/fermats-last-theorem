import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import P2M.Util
import P2M.Sol.S_HeckeEis_linearIndependent_coeffH1par_map_rat_complex

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.linearIndependent_coeffH1par_map_rat_complex (n : ℕ) (Γ : Subgroup SL(2, ℤ))
    (Ψ : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℚ n).comp Γ.subtype) →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype))
    (hΨ : ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℚ n).comp Γ.subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype)),
        (∀ g : Γ, ((w : Γ → ↥(HeckeEis.BinaryForm ℂ n)) g : MvPolynomial (Fin 2) ℂ)
            = MvPolynomial.map (algebraMap ℚ ℂ)
                (((z : Γ → ↥(HeckeEis.BinaryForm ℚ n)) g : MvPolynomial (Fin 2) ℚ))) ∧
        Ψ (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w)
    {ι : Type*} (y : ι → HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℚ n).comp Γ.subtype)) (hy : LinearIndependent ℚ y) :
    LinearIndependent ℂ (fun i => Ψ (y i)) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_linearIndependent_coeffH1par_map_rat_complex.solution
