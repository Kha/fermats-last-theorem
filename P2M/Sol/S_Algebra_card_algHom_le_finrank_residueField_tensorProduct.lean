import Mathlib
import P2M.Util
namespace P2MW.S_Algebra_card_algHom_le_finrank_residueField_tensorProduct

set_option autoImplicit false

open TensorProduct

theorem solution
    (R : Type*) [CommRing R] [IsLocalRing R]
    (B : Type*) [CommRing B] [Algebra R B] [Module.Finite R B]
    (Ω : Type*) [Field Ω] [Algebra R Ω] :
    Finite (B →ₐ[R] Ω) ∧
      Nat.card (B →ₐ[R] Ω) ≤
        Module.finrank (IsLocalRing.ResidueField R)
          (TensorProduct R (IsLocalRing.ResidueField R) B) := by
  classical
  set κ := IsLocalRing.ResidueField R with hκ

  set d := Module.finrank κ (TensorProduct R κ B) with hd
  let bκ : Module.Basis (Fin d) κ (TensorProduct R κ B) := Module.finBasis κ (TensorProduct R κ B)
  have hsurj : Function.Surjective (TensorProduct.mk R κ B 1) :=
    TensorProduct.mk_surjective R B κ Ideal.Quotient.mk_surjective
  choose f hf using fun i : Fin d => hsurj (bκ i)
  have hspanR : Submodule.span R (Set.range f) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis f bκ (fun i => hf i)

  have hspanΩ : Submodule.span Ω (Set.range fun i : Fin d => (1 : Ω) ⊗ₜ[R] f i) = ⊤ := by
    have h := Submodule.baseChange_span (R := R) (M := B) Ω (Set.range f)
    rw [hspanR, Submodule.baseChange_top] at h
    rw [← Set.range_comp] at h
    exact h.symm
  have hfinΩ : Module.finrank Ω (TensorProduct R Ω B) ≤ d := by
    have h1 := finrank_range_le_card (R := Ω) (M := TensorProduct R Ω B)
      (fun i : Fin d => (1 : Ω) ⊗ₜ[R] f i)
    rw [Set.finrank, hspanΩ, finrank_top, Fintype.card_fin] at h1
    exact h1

  let e : (B →ₐ[R] Ω) ≃ (TensorProduct R Ω B →ₐ[Ω] Ω) := AlgHom.liftEquiv R Ω B Ω
  have hli : LinearIndependent Ω
      (AlgHom.toLinearMap : (TensorProduct R Ω B →ₐ[Ω] Ω) → TensorProduct R Ω B →ₗ[Ω] Ω) :=
    linearIndependent_algHom_toLinearMap Ω (TensorProduct R Ω B) Ω
  haveI hfin : Finite (TensorProduct R Ω B →ₐ[Ω] Ω) := hli.finite_of_isNoetherian
  haveI : Finite (B →ₐ[R] Ω) := Finite.of_equiv _ e.symm
  refine ⟨inferInstance, ?_⟩
  haveI : Fintype (TensorProduct R Ω B →ₐ[Ω] Ω) := Fintype.ofFinite _
  have hcard : Fintype.card (TensorProduct R Ω B →ₐ[Ω] Ω) ≤
      Module.finrank Ω (TensorProduct R Ω B →ₗ[Ω] Ω) := hli.fintype_card_le_finrank
  have hdual : Module.finrank Ω (TensorProduct R Ω B →ₗ[Ω] Ω) = Module.finrank Ω (TensorProduct R Ω B) :=
    Subspace.dual_finrank_eq
  calc Nat.card (B →ₐ[R] Ω) = Nat.card (TensorProduct R Ω B →ₐ[Ω] Ω) := Nat.card_congr e
    _ = Fintype.card (TensorProduct R Ω B →ₐ[Ω] Ω) := Nat.card_eq_fintype_card
    _ ≤ Module.finrank Ω (TensorProduct R Ω B →ₗ[Ω] Ω) := hcard
    _ = Module.finrank Ω (TensorProduct R Ω B) := hdual
    _ ≤ d := hfinΩ
