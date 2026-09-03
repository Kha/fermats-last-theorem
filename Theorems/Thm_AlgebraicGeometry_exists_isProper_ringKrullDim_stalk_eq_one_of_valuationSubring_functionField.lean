import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField
attribute [-instance] AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
attribute [-simp] AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField
    (k : Type u) [Field k] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsIntegral P] [LocallyOfFiniteType p]
    (O : ValuationSubring P.functionField) (hO : O ≠ ⊤)
    (ℓ₀ : Spec (CommRingCat.of O) ⟶ P)
    (hℓ₀ : Spec.map (CommRingCat.ofHom (algebraMap O P.functionField)) ≫ ℓ₀ =
      P.fromSpecStalk (genericPoint P))
    (d : ℕ) (hd : ((d + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim P)
    (f : Fin d → P.functionField) (hf : ∀ i, f i ∈ O)
    (hind : ∀ Q : MvPolynomial (Fin d) k,
      O.valuation (Q.eval₂ ((P.presheaf.germ ⊤ (genericPoint P) trivial).hom.comp
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)) f) < 1 → Q = 0) :
    ∃ (P' : Scheme.{u}) (β : P' ⟶ P) (U : P.Opens) (s : (U : Scheme.{u}) ⟶ P')
      (ℓ : Spec (CommRingCat.of O) ⟶ P') (y' : P'),
      IsIntegral P' ∧ IsProper β ∧ (U : Set P).Nonempty ∧ IsOpenImmersion s ∧ s ≫ β = U.ι ∧
      Set.range s.base = β.base ⁻¹' (U : Set P) ∧
      ℓ ≫ β = ℓ₀ ∧ ℓ.base (IsLocalRing.closedPoint O) = y' ∧
      ringKrullDim (P'.presheaf.stalk y') = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField.solution
