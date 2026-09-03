import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_cover_comp_eq_comp_finComb_of_nsmul_eq_one_of_etale

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_cover_comp_eq_comp_finComb_of_nsmul_eq_one_of_etale
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative) (n : ℕ)

    (B : Type) [CommRing B] [Algebra S B] [Module.Finite S B] [Algebra.Etale S B]
    (ι : Spec (CommRingCat.of B) ⟶ A) (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S B)))
    (hιc : IsClosedImmersion ι)
    (hιn : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (y : SchemeHomOver t f),
      L.nsmul t n y = L.one t ↔ ∃ z : T ⟶ Spec (CommRingCat.of B), z ≫ ι = y.1)

    (S' : Type) [CommRing S'] [Algebra S S'] {m : ℕ}
    (P : Fin m → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S S'))) f)
    (hP : ∀ i, L.nsmul (Spec.map (CommRingCat.ofHom (algebraMap S S'))) n (P i) =
      L.one (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (hspan : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k)
      (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (sk.comp (algebraMap S S')))) f),
      L.nsmul (Spec.map (CommRingCat.ofHom (sk.comp (algebraMap S S')))) n Q =
        L.one (Spec.map (CommRingCat.ofHom (sk.comp (algebraMap S S')))) →
      ∃ c : Fin m → Fin n,
        Spec.map (CommRingCat.ofHom sk) ≫
          (L.finComb (Spec.map (CommRingCat.ofHom (algebraMap S S'))) P (fun i => (c i : ℕ))).1 = Q.1)

    (R : Type) [CommRing R] [Algebra S' R]
    (y : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap S' R).comp (algebraMap S S')))) f)
    (hy : L.nsmul (Spec.map (CommRingCat.ofHom ((algebraMap S' R).comp (algebraMap S S')))) n y =
      L.one (Spec.map (CommRingCat.ofHom ((algebraMap S' R).comp (algebraMap S S'))))) :
    ∃ (M : ℕ) (r : Fin M → R), Ideal.span (Set.range r) = ⊤ ∧ ∀ j, ∃ c : Fin m → Fin n,
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (r j)))) ≫ y.1 =
        Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away (r j))).comp (algebraMap S' R))) ≫
          (L.finComb (Spec.map (CommRingCat.ofHom (algebraMap S S'))) P (fun i => (c i : ℕ))).1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_cover_comp_eq_comp_finComb_of_nsmul_eq_one_of_etale.solution
