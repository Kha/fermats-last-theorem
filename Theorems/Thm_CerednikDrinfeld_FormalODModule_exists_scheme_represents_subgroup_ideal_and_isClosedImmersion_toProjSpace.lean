import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_scheme_represents_subgroup_ideal_and_isClosedImmersion_toProjSpace
attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient
attribute [-simp] MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem CerednikDrinfeld.FormalODModule.exists_scheme_represents_subgroup_ideal_and_isClosedImmersion_toProjSpace
    (p : ℕ) [Fact p.Prime] (B₀ : Type) [CommRing B₀] (Φ : FormalODModule p B₀) (N h : ℕ)
    [Module.Finite B₀ (FormalODModule.KerAlgebra (Φ.act ((p : Zp2 p) ^ N)))]
    [Module.Free B₀ (FormalODModule.KerAlgebra (Φ.act ((p : Zp2 p) ^ N)))]
    (hX : ∀ i, IsNilpotent
      (Ideal.Quotient.mk (Ideal.span (Set.range (Φ.act ((p : Zp2 p) ^ N)))) (MvPowerSeries.X i))) :
    ∃ (H : Scheme.{0}) (q : H ⟶ Spec (CommRingCat.of B₀))
      (pt : ∀ (S : Type) [CommRing S] [Algebra B₀ S],
        { I : Ideal (MvPowerSeries (Fin 2) S) //
            Module.Finite S (MvPowerSeries (Fin 2) S ⧸ I) ∧
            Module.Projective S (MvPowerSeries (Fin 2) S ⧸ I) ∧
            (∀ (κ : Type) [Field κ] (f : S →+* κ),
              Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ (I).map (MvPowerSeries.map f)) = p ^ h) ∧
            (∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) S) ^ q ∈ I) ∧
            (∀ f ∈ I, MvPowerSeries.constantCoeff f = 0) ∧
            (∀ f ∈ I, MvPowerSeries.subst (Φ.map (algebraMap B₀ S)).F.toPowerSeries f ∈
              Ideal.span
                ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S))) ''
                    (I : Set (MvPowerSeries (Fin 2) S)) ∪
                 (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S))) ''
                    (I : Set (MvPowerSeries (Fin 2) S)))) ∧
            (∀ (a : Zp2 p), ∀ f ∈ I, MvPowerSeries.subst ((Φ.map (algebraMap B₀ S)).act a) f ∈ I) ∧
            (∀ f ∈ I, MvPowerSeries.subst (Φ.map (algebraMap B₀ S)).varpi f ∈ I) ∧
            (∀ j : Fin 2, (Φ.map (algebraMap B₀ S)).act ((p : Zp2 p) ^ N) j ∈ I) } ≃
          {g : Spec (CommRingCat.of S) ⟶ H // g ≫ q = Spec.map (CommRingCat.ofHom (algebraMap B₀ S))})
      (hmap : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra B₀ S] [Algebra B₀ S'] (φ : S →ₐ[B₀] S')
        (I : { I : Ideal (MvPowerSeries (Fin 2) S) //
            Module.Finite S (MvPowerSeries (Fin 2) S ⧸ I) ∧
            Module.Projective S (MvPowerSeries (Fin 2) S ⧸ I) ∧
            (∀ (κ : Type) [Field κ] (f : S →+* κ),
              Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ (I).map (MvPowerSeries.map f)) = p ^ h) ∧
            (∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) S) ^ q ∈ I) ∧
            (∀ f ∈ I, MvPowerSeries.constantCoeff f = 0) ∧
            (∀ f ∈ I, MvPowerSeries.subst (Φ.map (algebraMap B₀ S)).F.toPowerSeries f ∈
              Ideal.span
                ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S))) ''
                    (I : Set (MvPowerSeries (Fin 2) S)) ∪
                 (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S))) ''
                    (I : Set (MvPowerSeries (Fin 2) S)))) ∧
            (∀ (a : Zp2 p), ∀ f ∈ I, MvPowerSeries.subst ((Φ.map (algebraMap B₀ S)).act a) f ∈ I) ∧
            (∀ f ∈ I, MvPowerSeries.subst (Φ.map (algebraMap B₀ S)).varpi f ∈ I) ∧
            (∀ j : Fin 2, (Φ.map (algebraMap B₀ S)).act ((p : Zp2 p) ^ N) j ∈ I) }),
        Module.Finite S' (MvPowerSeries (Fin 2) S' ⧸ (I.1.map (MvPowerSeries.map (φ : S →+* S')))) ∧
            Module.Projective S' (MvPowerSeries (Fin 2) S' ⧸ (I.1.map (MvPowerSeries.map (φ : S →+* S')))) ∧
            (∀ (κ : Type) [Field κ] (f : S' →+* κ),
              Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ ((I.1.map (MvPowerSeries.map (φ : S →+* S')))).map (MvPowerSeries.map f)) = p ^ h) ∧
            (∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) S') ^ q ∈ (I.1.map (MvPowerSeries.map (φ : S →+* S')))) ∧
            (∀ f ∈ (I.1.map (MvPowerSeries.map (φ : S →+* S'))), MvPowerSeries.constantCoeff f = 0) ∧
            (∀ f ∈ (I.1.map (MvPowerSeries.map (φ : S →+* S'))), MvPowerSeries.subst (Φ.map (algebraMap B₀ S')).F.toPowerSeries f ∈
              Ideal.span
                ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S'))) ''
                    ((I.1.map (MvPowerSeries.map (φ : S →+* S'))) : Set (MvPowerSeries (Fin 2) S')) ∪
                 (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S'))) ''
                    ((I.1.map (MvPowerSeries.map (φ : S →+* S'))) : Set (MvPowerSeries (Fin 2) S')))) ∧
            (∀ (a : Zp2 p), ∀ f ∈ (I.1.map (MvPowerSeries.map (φ : S →+* S'))), MvPowerSeries.subst ((Φ.map (algebraMap B₀ S')).act a) f ∈ (I.1.map (MvPowerSeries.map (φ : S →+* S')))) ∧
            (∀ f ∈ (I.1.map (MvPowerSeries.map (φ : S →+* S'))), MvPowerSeries.subst (Φ.map (algebraMap B₀ S')).varpi f ∈ (I.1.map (MvPowerSeries.map (φ : S →+* S')))) ∧
            (∀ j : Fin 2, (Φ.map (algebraMap B₀ S')).act ((p : Zp2 p) ^ N) j ∈ (I.1.map (MvPowerSeries.map (φ : S →+* S'))))),
      (∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra B₀ S] [Algebra B₀ S'] (φ : S →ₐ[B₀] S')
        (I : { I : Ideal (MvPowerSeries (Fin 2) S) //
            Module.Finite S (MvPowerSeries (Fin 2) S ⧸ I) ∧
            Module.Projective S (MvPowerSeries (Fin 2) S ⧸ I) ∧
            (∀ (κ : Type) [Field κ] (f : S →+* κ),
              Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ (I).map (MvPowerSeries.map f)) = p ^ h) ∧
            (∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) S) ^ q ∈ I) ∧
            (∀ f ∈ I, MvPowerSeries.constantCoeff f = 0) ∧
            (∀ f ∈ I, MvPowerSeries.subst (Φ.map (algebraMap B₀ S)).F.toPowerSeries f ∈
              Ideal.span
                ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S))) ''
                    (I : Set (MvPowerSeries (Fin 2) S)) ∪
                 (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S))) ''
                    (I : Set (MvPowerSeries (Fin 2) S)))) ∧
            (∀ (a : Zp2 p), ∀ f ∈ I, MvPowerSeries.subst ((Φ.map (algebraMap B₀ S)).act a) f ∈ I) ∧
            (∀ f ∈ I, MvPowerSeries.subst (Φ.map (algebraMap B₀ S)).varpi f ∈ I) ∧
            (∀ j : Fin 2, (Φ.map (algebraMap B₀ S)).act ((p : Zp2 p) ^ N) j ∈ I) }),
        (pt S' ⟨I.1.map (MvPowerSeries.map (φ : S →+* S')), hmap S S' φ I⟩).1 =
          Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (pt S I).1) ∧
      ∃ (m : ℕ) (ιP : H ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) B₀)),
        IsClosedImmersion ιP ∧ ιP ≫ ProjSpace.π B₀ m = q := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_scheme_represents_subgroup_ideal_and_isClosedImmersion_toProjSpace.solution
