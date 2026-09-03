import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_delta_hom_comp_eq_zero

set_option autoImplicit false
open CategoryTheory

theorem Rep.delta_hom_comp_eq_zero {G : Type} [Group G] (R : Rep ℤ G)
    {T : ShortComplex (Rep ℤ G)} (hT : (T.map (ihom R)).ShortExact) (s : R ⟶ T.X₂) :
    (groupCohomology.δ hT 0 1 rfl).hom
        ((groupCohomology.H0Iso ((ihom R).obj T.X₃)).inv ((Representation.linHom.invariantsEquivRepHom R T.X₃).symm (s ≫ T.g))) = 0 := by p2m_exact_reverting @_root_.P2MW.S_Rep_delta_hom_comp_eq_zero.solution
