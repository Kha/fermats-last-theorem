import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_finite_etale_faithfullyFlat_finComb_basis_of_forall_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_finite_etale_faithfullyFlat_finComb_basis_of_forall_isAlgClosed
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative) (n m : ℕ)

    (B : Type) [CommRing B] [Algebra S B] [Module.Finite S B] [Algebra.Etale S B]
    (ι : Spec (CommRingCat.of B) ⟶ A) (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S B)))
    (hιc : IsClosedImmersion ι)
    (hιn : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (y : SchemeHomOver t f),
      L.nsmul t n y = L.one t ↔ ∃ z : T ⟶ Spec (CommRingCat.of B), z ≫ ι = y.1)

    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
      ∃ P : Fin m → SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f,
        (∀ i, L.nsmul (Spec.map (CommRingCat.ofHom sk)) n (P i) = L.one (Spec.map (CommRingCat.ofHom sk))) ∧
        (∀ c c' : Fin m → Fin n,
          L.finComb (Spec.map (CommRingCat.ofHom sk)) P (fun i => (c i : ℕ)) =
            L.finComb (Spec.map (CommRingCat.ofHom sk)) P (fun i => (c' i : ℕ)) → c = c') ∧
        (∀ Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f,
          L.nsmul (Spec.map (CommRingCat.ofHom sk)) n Q = L.one (Spec.map (CommRingCat.ofHom sk)) →
          ∃ c : Fin m → Fin n, L.finComb (Spec.map (CommRingCat.ofHom sk)) P (fun i => (c i : ℕ)) = Q)) :
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra S S') (_ : Module.Finite S S') (_ : Algebra.Etale S S')
      (_ : Module.FaithfullyFlat S S')
      (P : Fin m → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S S'))) f),
      (∀ i, L.nsmul (Spec.map (CommRingCat.ofHom (algebraMap S S'))) n (P i) =
        L.one (Spec.map (CommRingCat.ofHom (algebraMap S S')))) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k) (c c' : Fin m → Fin n),
        Spec.map (CommRingCat.ofHom sk) ≫
            (L.finComb (Spec.map (CommRingCat.ofHom (algebraMap S S'))) P (fun i => (c i : ℕ))).1 =
          Spec.map (CommRingCat.ofHom sk) ≫
            (L.finComb (Spec.map (CommRingCat.ofHom (algebraMap S S'))) P (fun i => (c' i : ℕ))).1 → c = c') ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k)
        (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (sk.comp (algebraMap S S')))) f),
        L.nsmul (Spec.map (CommRingCat.ofHom (sk.comp (algebraMap S S')))) n Q =
          L.one (Spec.map (CommRingCat.ofHom (sk.comp (algebraMap S S')))) →
        ∃ c : Fin m → Fin n,
          Spec.map (CommRingCat.ofHom sk) ≫
            (L.finComb (Spec.map (CommRingCat.ofHom (algebraMap S S'))) P (fun i => (c i : ℕ))).1 = Q.1) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_finite_etale_faithfullyFlat_finComb_basis_of_forall_isAlgClosed.solution
