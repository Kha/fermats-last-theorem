import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_AlgFunctor_existsUnique_lift_quotient_of_forall_existsUnique_lift_of_ker_sq_eq_bot

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.AlgFunctor.existsUnique_lift_quotient_of_forall_existsUnique_lift_of_ker_sq_eq_bot
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)

    (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))

    (C : Type) [CommRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π))

    (PR : CerednikDrinfeld.FormalOmega.AlgFunctor C)
    (toM : ∀ (S : Type) [CommRing S] [Algebra C S],
      PR.obj S → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C S))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))

    (hR0 : (∀ (S S' : Type) [CommRing S] [Algebra C S] [CommRing S'] [Algebra C S'] (φ : S →ₐ[C] S') (x : PR.obj S),
          (toM S' (PR.map φ x)).1 = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (toM S x).1))

    (het : (∀ (S S₀ : Type) [CommRing S] [IsNoetherianRing S] [Algebra C S] [CommRing S₀] [Algebra C S₀] (p : S →ₐ[C] S₀),
          Function.Surjective p → RingHom.ker (p : S →+* S₀) ^ 2 = ⊥ →
          ∀ (x₀ : PR.obj S₀) (t : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C S))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
          Spec.map (CommRingCat.ofHom (p : S →+* S₀)) ≫ t.1 = (toM S₀ x₀).1 →
          ∃! x : PR.obj S, PR.map p x = x₀ ∧ toM S x = t)) :

    (∀ (T : Type) [CommRing T] [IsNoetherianRing T] [Algebra C T]
          (xb : PR.obj (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))
          (t : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ t.1 =
            (toM _ xb).1 →
          ∃! x : PR.obj T,
            PR.map (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) x = xb ∧ toM T x = t) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_AlgFunctor_existsUnique_lift_quotient_of_forall_existsUnique_lift_of_ker_sq_eq_bot.solution
