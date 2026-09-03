import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_ThetaPt_exists_bijective_thetaGroup_antiHom_of_compatible
attribute [-instance] AlgebraicGeometry.ThetaLevel.Heis.instInv AlgebraicGeometry.ThetaLevel.Heis.Gam.instFinite AlgebraicGeometry.ThetaLevel.Heis.instMul AlgebraicGeometry.ThetaLevel.Heis.Gam.instFintype AlgebraicGeometry.ThetaLevel.Heis.instGroup AlgebraicGeometry.ThetaLevel.Heis.instDecidableEq AlgebraicGeometry.ThetaLevel.Heis.instOne AlgebraicGeometry.ThetaLevel.Heis.instFintype
attribute [-simp] AlgebraicGeometry.ThetaLevel.Heis.theta_h AlgebraicGeometry.ThetaLevel.Heis.mk.injEq AlgebraicGeometry.ThetaLevel.Heis.one_k AlgebraicGeometry.ThetaLevel.Heis.mk.sizeOf_spec AlgebraicGeometry.ThetaLevel.Heis.mul_a AlgebraicGeometry.ThetaLevel.Heis.eta_a AlgebraicGeometry.ThetaLevel.Heis.mul_h AlgebraicGeometry.ThetaLevel.Heis.inv_k AlgebraicGeometry.ThetaLevel.Heis.mul_k AlgebraicGeometry.ThetaLevel.Heis.one_a AlgebraicGeometry.ThetaLevel.Heis.cen_a AlgebraicGeometry.ThetaLevel.Heis.one_h AlgebraicGeometry.ThetaLevel.Heis.theta_k AlgebraicGeometry.ThetaLevel.Heis.cen_k AlgebraicGeometry.ThetaLevel.Heis.theta_a AlgebraicGeometry.ThetaLevel.Heis.inv_h AlgebraicGeometry.ThetaLevel.diagOp_apply AlgebraicGeometry.ThetaLevel.Heis.cen_h AlgebraicGeometry.ThetaLevel.Heis.eta_h AlgebraicGeometry.ThetaLevel.shiftOp_apply AlgebraicGeometry.ThetaLevel.Heis.inv_a AlgebraicGeometry.ThetaLevel.Heis.eta_k

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped commutatorElement

theorem AlgebraicGeometry.Polarisation.ThetaPt.exists_bijective_thetaGroup_antiHom_of_compatible
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (𝓛 : A.Modules)
    {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of S))
    (L' : RelativeGroupLaw K (pullback.snd f t)) (hc' : L'.IsCommutative)
    (hL' : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' (pullback.snd f t)),
      (L'.mul t' P Q).1 ≫ pullback.fst f t =
        (L.mul (t' ≫ t)
          ⟨P.1 ≫ pullback.fst f t, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f t, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) :
    ∃ Φ : ThetaPt f L 𝓛 t →
        RiemannForm.thetaGroup (pullback.snd f t) L' hc'
          ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛),
      Function.Bijective Φ ∧ Φ 1 = 1 ∧ (∀ θ θ' : ThetaPt f L 𝓛 t, Φ (θ * θ') = Φ θ' * Φ θ) ∧
      (∀ θ : ThetaPt f L 𝓛 t,
        (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd
          (RiemannForm.thetaGroup.pt (pullback.snd f t) L' hc' _ (Φ θ)))).1 ≫
            pullback.fst f t = θ.pt.1) ∧
      (∀ (θ θ' : ThetaPt f L 𝓛 t) (c : K),
        RiemannForm.thetaGroup.IsScalarElt (pullback.snd f t) L' hc' _ ⁅Φ θ, Φ θ'⁆ c →
          ∀ s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤),
            θ.act (θ'.act s) = baseScalar f t c • θ'.act (θ.act s)) ∧
      (∀ c : Kˣ, RiemannForm.thetaGroup.IsScalarElt (pullback.snd f t) L' hc' _
          (Φ (ThetaPt.ofScalar c)) ((c⁻¹ : Kˣ) : K)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_ThetaPt_exists_bijective_thetaGroup_antiHom_of_compatible.solution
