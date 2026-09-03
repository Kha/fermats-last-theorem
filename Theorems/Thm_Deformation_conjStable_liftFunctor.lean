import Mathlib
import Definitions.Def_Deformations_ConjQuotSubfunctor
import P2M.Util
import P2M.Sol.S_Deformation_conjStable_liftFunctor

open CategoryTheory IsLocalRing

universe u v
theorem Deformation.conjStable_liftFunctor {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] {n : Type} [Fintype n] [DecidableEq n]
  {G : Type u} [Group G] [TopologicalSpace G]
  (ρ₀ : (Deformation.repnFunctor n G 𝓞).obj Deformation.ProartinianCat.residueField) :
  Deformation.ConjStable n (Deformation.liftFunctor n G 𝓞 ρ₀) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_conjStable_liftFunctor.solution
