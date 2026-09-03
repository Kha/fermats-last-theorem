import Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_exists_symmetryGroup_semilinearAut_invariantFieldOf

set_option autoImplicit false

open CerednikDrinfeld.Mumford AlgebraicCurve

theorem CerednikDrinfeld.Mumford.exists_symmetryGroup_semilinearAut_invariantFieldOf
    (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
    [MulSemiringAction G M] [SMulCommClass G K M] [IsDomain M]
    (D : Type) [Group D] (amb : D →* Mumford.AmbientSemilinearAut K G M) (χ : D →* Multiplicative (ZMod 2)) :
    ∃ (S : Type) (_ : Group S) (scalar : S →* D) (ιS : D →* S) (_ : ∀ τ, scalar (ιS τ) = τ) (σ₀ σ₁ : S)
      (χS : S →* Multiplicative (ZMod 2)),

      (∀ σ : S, ∃ (τ : D) (u v : ℕ), σ = ιS τ * σ₀ ^ u * σ₁ ^ v) ∧
      scalar σ₀ = 1 ∧ scalar σ₁ = 1 ∧ σ₀ * σ₀ = 1 ∧ σ₁ * σ₁ = 1 ∧
      σ₀ * σ₁ = σ₁ * σ₀ ∧ (∀ τ, ιS τ * σ₀ = σ₀ * ιS τ) ∧ (∀ τ, ιS τ * σ₁ = σ₁ * ιS τ) ∧

      (∀ (H : Type) [Group H] (f : D →* H) (h₀ h₁ : H),
        h₀ * h₀ = 1 → h₁ * h₁ = 1 → h₀ * h₁ = h₁ * h₀ → (∀ τ, f τ * h₀ = h₀ * f τ) → (∀ τ, f τ * h₁ = h₁ * f τ) →
        ∃ F : S →* H, (∀ τ, F (ιS τ) = f τ) ∧ F σ₀ = h₀ ∧ F σ₁ = h₁) ∧

      (∀ τ, χS (ιS τ) = χ τ) ∧ χS σ₀ ≠ 1 ∧ χS σ₁ = 1 ∧

      ∀ (Δ : Subgroup G) (w wbar : G) (hw : w ∈ Subgroup.normalizer ((Δ : Subgroup G) : Set G))
        (hwbar : wbar ∈ Subgroup.normalizer ((Δ : Subgroup G) : Set G))
        (hww : ∀ x ∈ Mumford.invariantFieldOf K G M Δ, (w * w) • x = x)
        (hbb : ∀ x ∈ Mumford.invariantFieldOf K G M Δ, (wbar * wbar) • x = x)
        (hwb : ∀ x ∈ Mumford.invariantFieldOf K G M Δ, (w * wbar) • x = (wbar * w) • x),
        ∃ galC : S →* AlgebraicCurve.SemilinearAut K ↥(Mumford.invariantFieldOf K G M Δ),
          (∀ (σ : S) (c : K), SemilinearAut.baseAut (galC σ) c =
            SemilinearAut.baseAut (Mumford.AmbientSemilinearAut.coeffActOf Δ (amb (scalar σ))) c) ∧
          (∀ (τ : D) (y : ↥(Mumford.invariantFieldOf K G M Δ)),
            ((galC (ιS τ) • y : ↥(Mumford.invariantFieldOf K G M Δ)) : FractionRing M) =
              (if χ τ = 1 then (1 : G) else w) • Mumford.AmbientSemilinearAut.fracMap (amb τ) (y : FractionRing M)) ∧
          (∀ y : ↥(Mumford.invariantFieldOf K G M Δ), ((galC σ₀ • y : ↥(Mumford.invariantFieldOf K G M Δ)) : FractionRing M) = w • (y : FractionRing M)) ∧
          (∀ y : ↥(Mumford.invariantFieldOf K G M Δ), ((galC σ₁ • y : ↥(Mumford.invariantFieldOf K G M Δ)) : FractionRing M) = wbar • (y : FractionRing M)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_exists_symmetryGroup_semilinearAut_invariantFieldOf.solution
