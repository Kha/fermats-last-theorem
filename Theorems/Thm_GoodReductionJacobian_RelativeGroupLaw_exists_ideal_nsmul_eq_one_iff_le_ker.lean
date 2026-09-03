import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_ideal_nsmul_eq_one_iff_le_ker

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.RelativeGroupLaw.exists_ideal_nsmul_eq_one_iff_le_ker
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f) (n : ℕ)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f) :
    ∃ I : Ideal S, ∀ (S' : Type) [CommRing S'] (φ : S →+* S'),
      L.nsmul (Spec.map (CommRingCat.ofHom φ)) n
          (schemeHomOverComp (Spec.map (CommRingCat.ofHom φ)) (Category.comp_id _) P) =
        L.one (Spec.map (CommRingCat.ofHom φ)) ↔ I ≤ RingHom.ker φ := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_ideal_nsmul_eq_one_iff_le_ker.solution
