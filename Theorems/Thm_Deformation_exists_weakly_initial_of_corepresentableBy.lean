import Mathlib
import Definitions.Def_Deformations_LiftFunctor
import P2M.Util
import P2M.Sol.S_Deformation_exists_weakly_initial_of_corepresentableBy

set_option autoImplicit false
open CategoryTheory

universe u
theorem Deformation.exists_weakly_initial_of_corepresentableBy
    {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G] [TopologicalSpace G]
    {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]
    {F : Subfunctor (Deformation.repnFunctor n G 𝓞)} {R : Deformation.ProartinianCat 𝓞}
    (e : F.toFunctor.CorepresentableBy R) :
    ∃ T : F.toFunctor.Elements, ∀ X : F.toFunctor.Elements, Nonempty (T ⟶ X) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_exists_weakly_initial_of_corepresentableBy.solution
