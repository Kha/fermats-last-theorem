import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_subsingleton_H1_specialLinearGroup_fin_two_traceZero_algebra_of_charP_three

set_option autoImplicit false

open Matrix MatrixGroups groupCohomology

theorem groupCohomology.subsingleton_H1_specialLinearGroup_fin_two_traceZero_algebra_of_charP_three
    {F : Type} [Field F] [Finite F] [CharP F 3]
    {k : Type} [Field k] [Finite k] [Algebra F k]
    (A : Rep F SL(2, F)) (e : A →ₗ[F] Matrix (Fin 2) (Fin 2) k)
    (he_inj : Function.Injective e)
    (he_range : LinearMap.range e =
      (LinearMap.ker (Matrix.traceLinearMap (Fin 2) k k)).restrictScalars F)
    (he_act : ∀ (g : SL(2, F)) (a : A),
      e (A.ρ g a) = ((g : Matrix (Fin 2) (Fin 2) F).map (algebraMap F k)) * e a *
        (((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).map (algebraMap F k))) :
    Subsingleton (H1 A) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_subsingleton_H1_specialLinearGroup_fin_two_traceZero_algebra_of_charP_three.solution
