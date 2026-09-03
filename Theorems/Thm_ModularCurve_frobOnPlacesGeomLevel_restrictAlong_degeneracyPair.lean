import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_ModularCurve_frobOnPlacesGeomLevel_restrictAlong_degeneracyPair
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve ModularCurve

theorem ModularCurve.frobOnPlacesGeomLevel_restrictAlong_degeneracyPair
    (M s q' : ℕ) [NeZero M] [NeZero s] [Fact q'.Prime]
    (K : Type*) [Field K] [CharP K q']
    (data₁ : ModularPolynomialData q') (hKr₁ : KroneckerCongruence q' data₁)
    (data₂ : ModularPolynomialData q') (hKr₂ : KroneckerCongruence q' data₂)
    (φ : Fin 2 → (↥(modularFunctionFieldC K M) →ₐ[K] ↥(modularFunctionFieldC K (M * s))))
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
    (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC K (M * s))) : LaurentSeries K) = x)
    (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC K (M * s))) : LaurentSeries K) =
      qExpand K s x)
    (i : Fin 2) (w : Place K ↥(modularFunctionFieldC K (M * s))) :
    frobOnPlacesGeomLevel K M data₂ hKr₂ (w.restrictAlong (φ i) (hφ i)) =
      (frobOnPlacesGeomLevel K (M * s) data₁ hKr₁ w).restrictAlong (φ i) (hφ i) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_frobOnPlacesGeomLevel_restrictAlong_degeneracyPair.solution
