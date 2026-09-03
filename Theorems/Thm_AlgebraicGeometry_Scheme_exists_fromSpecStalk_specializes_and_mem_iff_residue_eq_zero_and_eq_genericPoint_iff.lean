import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_fromSpecStalk_specializes_and_mem_iff_residue_eq_zero_and_eq_genericPoint_iff

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_fromSpecStalk_specializes_and_mem_iff_residue_eq_zero_and_eq_genericPoint_iff
    {X : Scheme.{u}} [IsIntegral X] (x : X) (P : Ideal (X.presheaf.stalk x)) [hP : P.IsPrime] :
    ∃ hη : (X.fromSpecStalk x).base ⟨P, hP⟩ ⤳ x,
      (∀ b : X.presheaf.stalk x,
        b ∈ P ↔ X.residue ((X.fromSpecStalk x).base ⟨P, hP⟩) ((X.presheaf.stalkSpecializes hη).hom b) = 0) ∧
      ((X.fromSpecStalk x).base ⟨P, hP⟩ = genericPoint X ↔ P = ⊥) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_fromSpecStalk_specializes_and_mem_iff_residue_eq_zero_and_eq_genericPoint_iff.solution
