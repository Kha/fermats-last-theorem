import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_exists_eq_comp_of_delta_hom_eq_zero

set_option autoImplicit false
open CategoryTheory

theorem Rep.exists_eq_comp_of_delta_hom_eq_zero {G : Type} [Group G] (R : Rep ℤ G)
    {T : ShortComplex (Rep ℤ G)} (hT : (T.map (ihom R)).ShortExact)
    (t : R ⟶ T.X₃) (ht : (groupCohomology.δ hT 0 1 rfl).hom
        ((groupCohomology.H0Iso ((ihom R).obj T.X₃)).inv ((Representation.linHom.invariantsEquivRepHom R T.X₃).symm t)) = 0) :
    ∃ s : R ⟶ T.X₂, t = s ≫ T.g := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_eq_comp_of_delta_hom_eq_zero.solution
