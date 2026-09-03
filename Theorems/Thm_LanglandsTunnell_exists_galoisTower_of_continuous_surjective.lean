import Mathlib
import Definitions.Def_LanglandsTunnell_GalRep
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective

open scoped MatrixGroups

theorem LanglandsTunnell.exists_galoisTower_of_continuous_surjective
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) (ZMod 3))
    (hcont : Continuous ρ) (hsurj : Function.Surjective ρ) :
    ∃ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : NumberField ↥L) (_ : IsGalois ℚ ↥L)
      (e : (↥L ≃ₐ[ℚ] ↥L) ≃* GL (Fin 2) (ZMod 3)), LanglandsTunnell.galRep e = ρ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_galoisTower_of_continuous_surjective.solution
