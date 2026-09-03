import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_flat_surjective_locallyQuasiFinite_of_locallyQuasiFinite_primePow
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.nsmul_flat_surjective_locallyQuasiFinite_of_locallyQuasiFinite_primePow
    (p : ℕ) [Fact p.Prime] {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of ℤ)} [Smooth g]
    (L : RelativeGroupLaw ℤ g) (hc : L.IsCommutative)
    (hconn : ∀ s : Spec (CommRingCat.of ℤ), _root_.IsPreconnected (g.base ⁻¹' {s}))
    (hA : ∀ s : Spec (CommRingCat.of ℤ), s.asIdeal = Ideal.span {(p : ℤ)} →
      ∀ k : ℕ, 0 < k → LocallyQuasiFinite ((L.fibre s).schemeNsmul (p ^ k)))
    (hB : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p → ∀ k : ℕ, 0 < k →
      LocallyQuasiFinite ((L.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))))).schemeNsmul (ℓ ^ k))) :
    (∀ n : ℕ, 0 < n → Flat (L.schemeNsmul n)) ∧ (∀ n : ℕ, 0 < n → Surjective (L.schemeNsmul n)) ∧
      (∀ n : ℕ, 0 < n → LocallyQuasiFinite (L.schemeNsmul n)) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_flat_surjective_locallyQuasiFinite_of_locallyQuasiFinite_primePow.solution
