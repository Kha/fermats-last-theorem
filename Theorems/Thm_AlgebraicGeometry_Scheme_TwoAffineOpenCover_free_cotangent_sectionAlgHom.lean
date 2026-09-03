import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_cotangent_sectionAlgHom

universe u

open CategoryTheory

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.free_cotangent_sectionAlgHom {R : Type u} [CommRing R] [IsLocalRing R] {X : AlgebraicGeometry.Scheme.{u}}
    {𝒱 : X.TwoAffineOpenCover} {c : X ⟶ AlgebraicGeometry.Spec (.of R)}
    [AlgebraicGeometry.SmoothOfRelativeDimension 1 c]
    (σ : AlgebraicGeometry.Spec (.of R) ⟶ X) (hσ : σ ≫ c = 𝟙 _) (hU : Set.range σ.base ⊆ (𝒱.U0 : Set X)) :
    Module.Free R (RingHom.ker
        (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom σ hσ hU).toRingHom).Cotangent ∧
      Module.finrank R (RingHom.ker
        (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom σ hσ hU).toRingHom).Cotangent = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_cotangent_sectionAlgHom.solution
