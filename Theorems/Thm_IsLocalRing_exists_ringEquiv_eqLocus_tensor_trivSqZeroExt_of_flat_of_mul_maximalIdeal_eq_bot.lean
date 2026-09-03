import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_ringEquiv_eqLocus_tensor_trivSqZeroExt_of_flat_of_mul_maximalIdeal_eq_bot

set_option autoImplicit false

open TensorProduct IsLocalRing

universe u
theorem IsLocalRing.exists_ringEquiv_eqLocus_tensor_trivSqZeroExt_of_flat_of_mul_maximalIdeal_eq_bot
    {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C] :
    let k := ResidueField T'
    let σ : C →+* C ⧸ I.map (algebraMap T' C) := Ideal.Quotient.mk _
    let P : Subring (C × C) := RingHom.eqLocus (σ.comp (RingHom.fst C C)) (σ.comp (RingHom.snd C C))
    let toCk : C →+* k ⊗[T'] C := Algebra.TensorProduct.includeRight.toRingHom
    let E := (k ⊗[T'] C) ⊗[k] TrivSqZeroExt k V
    let aug : E →+* k ⊗[T'] C :=
      (Algebra.TensorProduct.lift (AlgHom.id k (k ⊗[T'] C))
        ((Algebra.ofId k (k ⊗[T'] C)).comp (TrivSqZeroExt.fstHom k k V)) (fun _ _ => Commute.all _ _)).toRingHom
    let Q : Subring (C × E) := RingHom.eqLocus (toCk.comp (RingHom.fst C E)) (aug.comp (RingHom.snd C E))
    ∃ Θ : P ≃+* Q,
      (∀ x : P, ((Θ x : Q) : C × E).1 = (x : C × C).1) ∧
      (∀ (a : C) (ha : (a, a) ∈ P), ((Θ ⟨(a, a), ha⟩ : Q) : C × E).2 = toCk a ⊗ₜ (1 : TrivSqZeroExt k V)) ∧
      (∀ (v : V) (c : C) (h : ((0 : C), algebraMap T' C (ι v) * c) ∈ P),
        ((Θ ⟨((0 : C), algebraMap T' C (ι v) * c), h⟩ : Q) : C × E).2 = toCk c ⊗ₜ TrivSqZeroExt.inr v) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_ringEquiv_eqLocus_tensor_trivSqZeroExt_of_flat_of_mul_maximalIdeal_eq_bot.solution
