import Mathlib
import Definitions.Def_Deformations_ConjQuotSubfunctor
import P2M.Util
import P2M.Sol.S_Deformation_exists_weaklyInitial_elements_conjQuotSubfunctor

open CategoryTheory IsLocalRing

universe u v
theorem Deformation.exists_weaklyInitial_elements_conjQuotSubfunctor (n : Type) [Fintype n] [DecidableEq n] {G : Type u} [Group G]
  [TopologicalSpace G] {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]
  {F : CategoryTheory.Subfunctor (Deformation.repnFunctor n G 𝓞)} (T : F.toFunctor.Elements)
  (hT : ∀ (X : F.toFunctor.Elements), Nonempty (T ⟶ X)) :
  ∃ T', ∀ (X : (Deformation.conjQuotSubfunctor n F).toFunctor.Elements), Nonempty (T' ⟶ X) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_exists_weaklyInitial_elements_conjQuotSubfunctor.solution
