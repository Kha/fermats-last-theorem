import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_mulSemiringAction_integralClosure_inf_fixedPoints_of_isDiscreteValuationRing

set_option autoImplicit false

open scoped Pointwise

theorem ValuationSubring.exists_mulSemiringAction_integralClosure_inf_fixedPoints_of_isDiscreteValuationRing
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G] [MulSemiringAction G F] [FaithfulSMul G F]
    (P : ValuationSubring F) [IsDiscreteValuationRing ↥P] :
    ∃ (_ : MulSemiringAction G
          ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F))
      (𝔓 : Ideal ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F)),

      (∀ (g : G) (s : ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F)),
          g • algebraMap ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) F s = algebraMap ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) F (g • s)) ∧

      IsDiscreteValuationRing ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) ∧
      IsDedekindDomain ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) ∧
      (∀ x : F, x ∈ FixedPoints.subfield G F ↔
          ∃ a b : ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring), (b : F) ≠ 0 ∧ x * (b : F) = (a : F)) ∧

      IsDedekindDomain ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) ∧
      Module.Finite ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)
        ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) ∧
      Module.IsTorsionFree ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)
        ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) ∧
      IsFractionRing ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) F ∧
      IsGaloisGroup G ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)
        ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) ∧

      (∀ s : ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F), algebraMap ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) F s ∈ P) ∧

      𝔓.IsMaximal ∧
      (𝔓.comap (algebraMap ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)
          ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F))).IsMaximal ∧
      𝔓.comap (algebraMap ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F)) ≠ ⊥ ∧
      (∀ r : ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring),
          r ∈ 𝔓.comap (algebraMap ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)
            ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F)) ↔ (r : F) ∈ P.nonunits) ∧
      (∀ s : ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F),
          algebraMap ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) F s ∈ P.nonunits ↔ s ∈ 𝔓) ∧

      (∀ e : ↥P, ∃ s t : ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F),
          t ∉ 𝔓 ∧ (e : F) * algebraMap ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) F t = algebraMap ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) F s) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_mulSemiringAction_integralClosure_inf_fixedPoints_of_isDiscreteValuationRing.solution
