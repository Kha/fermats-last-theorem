import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_baseChange_chart_isPullback_of_isPullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.exists_baseChange_chart_isPullback_of_isPullback
    {O K Q : Type u} [CommRing O] [CommRing K] [CommRing Q] [Algebra O Q] [Algebra O K]
    {X XK : Scheme.{u}} (toO : X ⟶ Spec (CommRingCat.of O)) (toK : XK ⟶ Spec (CommRingCat.of K)) (pr : XK ⟶ X)
    (hpr : IsPullback pr toK toO (Spec.map (CommRingCat.ofHom (algebraMap O K))))
    (U : X.Opens) (f : (U : Scheme.{u}) ⟶ Spec (CommRingCat.of Q))
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O Q)) = U.ι ≫ toO) :
    ∃ fK : ((pr ⁻¹ᵁ U : XK.Opens) : Scheme.{u}) ⟶ Spec (CommRingCat.of (K ⊗[O] Q)),
      fK ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := O) (A := K) (B := Q)).toRingHom) = (pr ∣_ U) ≫ f ∧
      fK ≫ Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[O] Q))) = (pr ⁻¹ᵁ U).ι ≫ toK ∧
      IsPullback fK (pr ∣_ U) (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := O) (A := K) (B := Q)).toRingHom)) f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_baseChange_chart_isPullback_of_isPullback.solution
