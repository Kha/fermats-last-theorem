import Mathlib
import Definitions.Def_Deformations_MvPowerSeriesObj
import Definitions.Def_Deformations_TangentSubmodule
import P2M.Util
import P2M.Sol.S_Deformation_ProartinianCat_exists_surjective_mvPowerSeriesLift
attribute [-instance] Deformation.ProartinianCat.instFiniteResidueField Deformation.ProartinianCat.instCompactSpace

open CategoryTheory IsLocalRing

universe u v
theorem Deformation.ProartinianCat.exists_surjective_mvPowerSeriesLift {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]
    [IsNoetherianRing 𝓞] [Finite (IsLocalRing.ResidueField 𝓞)] [IsAdicComplete (IsLocalRing.maximalIdeal 𝓞) 𝓞]
    (R : Deformation.ProartinianCat 𝓞)
    [Module.Finite (IsLocalRing.ResidueField 𝓞) (Deformation.ProartinianCat.tangentSubmodule R)] :
    ∃ n : ℕ, n ≤ Module.finrank (IsLocalRing.ResidueField 𝓞) (Deformation.ProartinianCat.tangentSubmodule R) ∧
      ∃ f : Deformation.ProartinianCat.mvPowerSeriesObj 𝓞 n ⟶ R, Function.Surjective f.hom := by p2m_exact_reverting @_root_.P2MW.S_Deformation_ProartinianCat_exists_surjective_mvPowerSeriesLift.solution
