import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_exists_delta_hom_eq_of_map_ihom_map_eq_zero

set_option autoImplicit false
open CategoryTheory

theorem Rep.exists_delta_hom_eq_of_map_ihom_map_eq_zero {G : Type} [Group G] (R : Rep ℤ G)
    {T : ShortComplex (Rep ℤ G)} (hT : (T.map (ihom R)).ShortExact)
    (x : groupCohomology ((ihom R).obj T.X₁) 1)
    (hx : (groupCohomology.map (MonoidHom.id G) ((ihom R).map T.f) 1).hom x = 0) :
    ∃ t : R ⟶ T.X₃, (groupCohomology.δ hT 0 1 rfl).hom
        ((groupCohomology.H0Iso ((ihom R).obj T.X₃)).inv ((Representation.linHom.invariantsEquivRepHom R T.X₃).symm t)) = x := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_delta_hom_eq_of_map_ihom_map_eq_zero.solution
