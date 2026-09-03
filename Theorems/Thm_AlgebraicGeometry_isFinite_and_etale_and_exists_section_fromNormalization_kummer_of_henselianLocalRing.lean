import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isFinite_and_etale_and_exists_section_fromNormalization_kummer_of_henselianLocalRing

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

theorem AlgebraicGeometry.isFinite_and_etale_and_exists_section_fromNormalization_kummer_of_henselianLocalRing
    {R : Type u} [CommRing R] [IsNoetherianRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (k : ℕ) (hk : IsUnit ((k : ℕ) : R))
    (g : X.functionField) (hg : g ≠ 0)
    (r : ℕ) (U : Fin r → X.Opens) (hU : (⨆ a, U a) = ⊤) (h : Fin r → X.functionField) (hh : ∀ a, h a ≠ 0)
    (hdiv : ∀ a (x : X), x ∈ U a →
      g / h a ^ k ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range ∧
      h a ^ k / g ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range)
    (hcoc : ∀ a b (x : X), x ∈ U a → x ∈ U b →
      ∃ t ∈ IsLocalRing.maximalIdeal R, ∃ s ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range,
        h a = h b * (1 + AlgebraicCurve.SemistableModel.baseToFunctionField f t * s))
    (hconn : Function.Bijective
      (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).appTop) :
    let π := (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫
      X.fromSpecStalk (genericPoint X)).fromNormalization
    IsFinite π ∧ AlgebraicGeometry.Etale π ∧
      ∃ s₀ : pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ⟶ (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫
          X.fromSpecStalk (genericPoint X)).normalization,
        s₀ ≫ π = pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isFinite_and_etale_and_exists_section_fromNormalization_kummer_of_henselianLocalRing.solution
