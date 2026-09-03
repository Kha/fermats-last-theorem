import Mathlib
import Definitions.Def_Deformations_ProartinianCat
import P2M.Util
import P2M.Sol.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits
attribute [-instance] Deformation.ProartinianCat.instFiniteResidueField Deformation.ProartinianCat.instCompactSpace
attribute [-simp] CategoryTheory.Functor.corepresentableByOfIsInitial_homEquiv_symm_apply CategoryTheory.Functor.representableByOfIsInitial_homEquiv_symm_apply CategoryTheory.Functor.corepresentableByOfIsInitial_homEquiv_apply CategoryTheory.Functor.representableByOfIsInitial_homEquiv_apply

open CategoryTheory IsLocalRing

universe u v
theorem Deformation.ProartinianCat.isCorepresentable_of_preservesLimits {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]
  [Finite (IsLocalRing.ResidueField 𝓞)] (F : CategoryTheory.Functor (Deformation.ProartinianCat 𝓞) (Type u))
  [CategoryTheory.Limits.PreservesLimits F] : F.IsCorepresentable := by p2m_exact_reverting @_root_.P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.solution
