import Mathlib
import P2M.Util
import P2M.Sol.S_AdicCompletion_nonempty_ringEquiv_adicCompletion_tensorProduct_of_flat_of_map_maximalIdeal_eq_of_card_eq
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem AdicCompletion.nonempty_ringEquiv_adicCompletion_tensorProduct_of_flat_of_map_maximalIdeal_eq_of_card_eq
    (V : Type) [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (D₁ : Type) [CommRing D₁] [IsLocalRing D₁] [Algebra V D₁] [IsLocalHom (algebraMap V D₁)] [Module.Flat V D₁]
    (hVD₁ : (maximalIdeal V).map (algebraMap V D₁) = maximalIdeal D₁)
    [Module.Finite (ResidueField V) (ResidueField D₁)] [Algebra.IsSeparable (ResidueField V) (ResidueField D₁)]
    (W : Type) [CommRing W] [IsLocalRing W] [IsNoetherianRing W]
    (D₂ : Type) [CommRing D₂] [IsLocalRing D₂] [Algebra W D₂] [IsLocalHom (algebraMap W D₂)] [Module.Flat W D₂]
    (hWD₂ : (maximalIdeal W).map (algebraMap W D₂) = maximalIdeal D₂)
    [Module.Finite (ResidueField W) (ResidueField D₂)] [Algebra.IsSeparable (ResidueField W) (ResidueField D₂)]
    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra V C] [Algebra W C]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [Finite (C ⧸ 𝔫)]
    (h𝔫V : (maximalIdeal V).map (algebraMap V C) ≤ 𝔫) (h𝔫W : (maximalIdeal W).map (algebraMap W C) ≤ 𝔫)
    [IsNoetherianRing (C ⊗[V] D₁)] [IsNoetherianRing (C ⊗[W] D₂)]
    (x₁ : Ideal (C ⊗[V] D₁)) [x₁.IsMaximal] (hx₁ : 𝔫.map (algebraMap C (C ⊗[V] D₁)) ≤ x₁)
    (x₂ : Ideal (C ⊗[W] D₂)) [x₂.IsMaximal] (hx₂ : 𝔫.map (algebraMap C (C ⊗[W] D₂)) ≤ x₂)
    [Finite ((C ⊗[V] D₁) ⧸ x₁)] [Finite ((C ⊗[W] D₂) ⧸ x₂)]
    (hcard : Nat.card ((C ⊗[V] D₁) ⧸ x₁) = Nat.card ((C ⊗[W] D₂) ⧸ x₂)) :
    ∃ e : AdicCompletion x₁ (C ⊗[V] D₁) ≃+* AdicCompletion x₂ (C ⊗[W] D₂),
      ∀ c : C, e (algebraMap (C ⊗[V] D₁) (AdicCompletion x₁ (C ⊗[V] D₁)) (algebraMap C (C ⊗[V] D₁) c)) =
        algebraMap (C ⊗[W] D₂) (AdicCompletion x₂ (C ⊗[W] D₂)) (algebraMap C (C ⊗[W] D₂) c) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_nonempty_ringEquiv_adicCompletion_tensorProduct_of_flat_of_map_maximalIdeal_eq_of_card_eq.solution
