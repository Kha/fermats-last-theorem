import Mathlib
import P2M.Util
import P2M.Sol.S_AdicCompletion_exists_ringEquiv_mvPowerSeries_quotient_map_of_tensorProduct_of_flat

set_option autoImplicit false

open IsLocalRing TensorProduct MvPowerSeries

theorem AdicCompletion.exists_ringEquiv_mvPowerSeries_quotient_map_of_tensorProduct_of_flat
    (A₀ A : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A₀ A]
    [IsLocalHom (algebraMap A₀ A)] (hinj : Function.Injective (algebraMap A₀ A))
    [PerfectField (ResidueField A₀)]
    (B₀ : Type) [CommRing B₀] [Algebra A₀ B₀] [Algebra.FiniteType A₀ B₀] [Module.Flat A₀ B₀]
    (𝔪₀ : Ideal B₀) [𝔪₀.IsMaximal]
    (W₀ : Type) [CommRing W₀] [IsLocalRing W₀] [IsAdicComplete (maximalIdeal W₀) W₀] [Algebra A₀ W₀]

    (hW₀ : maximalIdeal W₀ = (maximalIdeal A₀).map (algebraMap A₀ W₀))
    (g₀ : MvPowerSeries (Fin 2) W₀)
    (e₀ : AdicCompletion 𝔪₀ B₀ ≃+* MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {g₀})
    (he₀ : ∀ a : A₀, e₀ (algebraMap B₀ (AdicCompletion 𝔪₀ B₀) (algebraMap A₀ B₀ a)) =
      Ideal.Quotient.mk (Ideal.span {g₀}) (C (algebraMap A₀ W₀ a)))
    (ψ : W₀ →+* AdicCompletion (maximalIdeal A) A)
    (hψ : ∀ a : A₀, ψ (algebraMap A₀ W₀ a) = algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap A₀ A a))
    (χ : B₀ →+* ResidueField A)
    (hχA₀ : ∀ a : A₀, χ (algebraMap A₀ B₀ a) = IsLocalRing.residue A (algebraMap A₀ A a))
    (hχ : ∀ (b : B₀) (w : W₀),
      e₀ (algebraMap B₀ (AdicCompletion 𝔪₀ B₀) b) - Ideal.Quotient.mk (Ideal.span {g₀}) (C w) ∈
        (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₀), X 1} ⊔ (maximalIdeal W₀).map (C : W₀ →+* MvPowerSeries (Fin 2) W₀)).map
          (Ideal.Quotient.mk (Ideal.span {g₀})) →
      ∃ a : A, IsLocalRing.residue A a = χ b ∧
        ψ w - algebraMap A (AdicCompletion (maximalIdeal A) A) a ∈
          (maximalIdeal A).map (algebraMap A (AdicCompletion (maximalIdeal A) A))) :
    let Â := AdicCompletion (maximalIdeal A) A
    let B := A ⊗[A₀] B₀
    let ev : B →+* ResidueField A :=
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A₀ A (ResidueField A))
        ({ toRingHom := χ, commutes' := fun a => by
            rw [IsScalarTower.algebraMap_apply A₀ A (ResidueField A)]; exact hχA₀ a } : B₀ →ₐ[A₀] ResidueField A)
        (fun _ _ => Commute.all _ _)).toRingHom
    let 𝔪 : Ideal B := RingHom.ker ev
    ∃ (_ : 𝔪.IsMaximal)
      (e : AdicCompletion 𝔪 B ≃+* MvPowerSeries (Fin 2) Â ⧸ Ideal.span {MvPowerSeries.map ψ g₀}),
      (∀ a : A, e (algebraMap B (AdicCompletion 𝔪 B) (algebraMap A B a)) =
        Ideal.Quotient.mk _ (C (algebraMap A Â a))) ∧
      (∀ (b : B₀) (s : MvPowerSeries (Fin 2) W₀),
        e₀ (algebraMap B₀ (AdicCompletion 𝔪₀ B₀) b) = Ideal.Quotient.mk (Ideal.span {g₀}) s →
        e (algebraMap B (AdicCompletion 𝔪 B) ((1 : A) ⊗ₜ[A₀] b)) =
          Ideal.Quotient.mk _ (MvPowerSeries.map ψ s)) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_exists_ringEquiv_mvPowerSeries_quotient_map_of_tensorProduct_of_flat.solution
