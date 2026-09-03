import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_restrictAlong_place_eq_smul_inv_and_inertiaDegAlong_eq_one_of_forall_mem_iff

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

theorem CerednikDrinfeld.Omega.restrictAlong_place_eq_smul_inv_and_inertiaDegAlong_eq_one_of_forall_mem_iff
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : Omega.PseudoUniformizer K₀ K)
    (G : Type) [Group G] (ρ : G →* PGL(2, K₀)) [IsDomain (Omega.HolRingOf ϖ ρ)]
    (Λ₁ Λ₂ : Subgroup G)
    (F₁ : Type) [Field F₁] [Algebra K F₁] (e₁ : F₁ ≃ₐ[K] ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁))
    (F₂ : Type) [Field F₂] [Algebra K F₂] (e₂ : F₂ ≃ₐ[K] ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₂))
    (g : G) (φ : F₂ →ₐ[K] F₁)
    (hφ : ∀ x : F₂, ((e₁ (φ x) : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁)) : FractionRing (Omega.HolRingOf ϖ ρ)) =
      g • ((e₂ x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₂)) : FractionRing (Omega.HolRingOf ϖ ρ)))
    (hφC : φ.toRingHom.IsIntegral)
    (pt₁ : ↥(Omega.upperHalfPlane K₀ K) → Place K F₁)
    (hpt₁ : ((∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (x : F₁),
        x ∈ (pt₁ z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 ∧ ((e₁ x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 →
          (pt₁ z).evalAt (e₁.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) =
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ∧
          (e₁.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt₁ z).toValuationSubring.nonunits ↔
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z = 0))))
    (pt₂ : ↥(Omega.upperHalfPlane K₀ K) → Place K F₂)
    (hpt₂ : ((∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (x : F₂),
        x ∈ (pt₂ z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 ∧ ((e₂ x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₂)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₂),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 →
          (pt₂ z).evalAt (e₂.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) =
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ∧
          (e₂.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt₂ z).toValuationSubring.nonunits ↔
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z = 0))))
    (z : ↥(Omega.upperHalfPlane K₀ K)) :
    (pt₁ z).restrictAlong φ hφC = pt₂ ((ρ g)⁻¹ • z) ∧ (pt₁ z).inertiaDegAlong φ hφC = 1 ∧
      ∀ n : ℤ, Divisor.pushforwardAlong φ hφC (Finsupp.single (pt₁ z) n) = Finsupp.single (pt₂ ((ρ g)⁻¹ • z)) n := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_restrictAlong_place_eq_smul_inv_and_inertiaDegAlong_eq_one_of_forall_mem_iff.solution
