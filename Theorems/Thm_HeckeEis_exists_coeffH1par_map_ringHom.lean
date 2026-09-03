import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_coeffH1par_map_ringHom

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_coeffH1par_map_ringHom {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') (n : ℕ)
    (Γ : Subgroup SL(2, ℤ)) :
    ∃ Φ : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R n).comp Γ.subtype) →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R' n).comp Γ.subtype),
      ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R n).comp Γ.subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R' n).comp Γ.subtype)),
        (∀ g : Γ, ((w : Γ → ↥(HeckeEis.BinaryForm R' n)) g : MvPolynomial (Fin 2) R')
            = MvPolynomial.map φ
                (((z : Γ → ↥(HeckeEis.BinaryForm R n)) g : MvPolynomial (Fin 2) R))) ∧
        Φ (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_coeffH1par_map_ringHom.solution
