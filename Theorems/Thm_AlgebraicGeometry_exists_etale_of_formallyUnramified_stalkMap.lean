import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_etale_of_formallyUnramified_stalkMap

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u
theorem AlgebraicGeometry.exists_etale_of_formallyUnramified_stalkMap
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [Smooth sX] [Smooth sY]
    (f : X ⟶ Y) (hf : f ≫ sY = sX)
    (σ : Spec (.of K) ⟶ X) (hσ : σ ≫ sX = 𝟙 _)
    (hfu : (f.stalkMap (σ.base (IsLocalRing.closedPoint K))).hom.FormallyUnramified)
    (hdim : Module.finrank
        (IsLocalRing.ResidueField (X.presheaf.stalk (σ.base (IsLocalRing.closedPoint K))))
        (IsLocalRing.CotangentSpace (X.presheaf.stalk (σ.base (IsLocalRing.closedPoint K)))) =
      Module.finrank
        (IsLocalRing.ResidueField
          (Y.presheaf.stalk (f.base (σ.base (IsLocalRing.closedPoint K)))))
        (IsLocalRing.CotangentSpace
          (Y.presheaf.stalk (f.base (σ.base (IsLocalRing.closedPoint K)))))) :
    ∃ U : X.Opens, σ.base (IsLocalRing.closedPoint K) ∈ U ∧ Etale (U.ι ≫ f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_etale_of_formallyUnramified_stalkMap.solution
