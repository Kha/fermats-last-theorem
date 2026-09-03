import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_PlaceTransport_under_smul
import Theorems.Thm_NumberField_PlaceTransport_transport_adicCompletionSemialgHom
import P2M.Util
namespace P2MW.S_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply

set_option autoImplicit false
open scoped NumberField.PlaceTransport

private theorem aux_semialgHom_under {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (a : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K)
    (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (hv : w'.under (NumberField.RingOfIntegers K) = v) :
    IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom K L
        (⟨w', hv⟩ : v.Extension (NumberField.RingOfIntegers L)) (a v)
      = IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom K L
        (⟨w', rfl⟩ : (w'.under (NumberField.RingOfIntegers K)).Extension (NumberField.RingOfIntegers L))
          (a (w'.under (NumberField.RingOfIntegers K))) := by
  subst hv
  rfl

theorem solution (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (x : NumberField.AdeleRing (NumberField.RingOfIntegers L) L)
    {w w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)} (h : σ • w = w') :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ x).2 w'
      = NumberField.PlaceTransport.transport σ h (x.2 w) := by
  letI : Algebra (NumberField.AdeleRing (NumberField.RingOfIntegers K) K) (NumberField.AdeleRing (NumberField.RingOfIntegers L) L) :=
    (M4aHerbrand.Bridge.genuineβ K L).toAlgebra

  have hact : ∀ y, (M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ y
      = M4aHerbrand.Bridge.genuineTensorEquiv K L
          ((Algebra.TensorProduct.congr AlgEquiv.refl σ) ((M4aHerbrand.Bridge.genuineTensorEquiv K L).symm y)) :=
    fun y => rfl
  obtain ⟨z, rfl⟩ := (M4aHerbrand.Bridge.genuineTensorEquiv K L).surjective x
  rw [hact, AlgEquiv.symm_apply_apply]
  induction z using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
    show (0 : w'.adicCompletion L) = NumberField.PlaceTransport.transport σ h 0
    rw [map_zero]
  | add z₁ z₂ h₁ h₂ =>
    simp only [map_add]
    show ((M4aHerbrand.Bridge.genuineTensorEquiv K L) ((Algebra.TensorProduct.congr AlgEquiv.refl σ) z₁)).2 w'
        + ((M4aHerbrand.Bridge.genuineTensorEquiv K L) ((Algebra.TensorProduct.congr AlgEquiv.refl σ) z₂)).2 w'
      = NumberField.PlaceTransport.transport σ h
        (((M4aHerbrand.Bridge.genuineTensorEquiv K L) z₁).2 w + ((M4aHerbrand.Bridge.genuineTensorEquiv K L) z₂).2 w)
    rw [h₁, h₂, map_add]
  | tmul a l =>

    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]

    have hte : ∀ m : L, M4aHerbrand.Bridge.genuineTensorEquiv K L (a ⊗ₜ[K] m)
        = M4aHerbrand.Bridge.genuineβ K L a * algebraMap L (NumberField.AdeleRing (NumberField.RingOfIntegers L) L) m := by
      intro m
      rw [← M4aHerbrand.Bridge.genuineTensorEquiv_tmul_one K L, ← M4aHerbrand.Bridge.genuineTensorEquiv_one_tmul K L,
        ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    simp only [AlgEquiv.coe_algHom, AlgEquiv.coe_refl, id_eq]
    rw [hte, hte]

    show (M4aHerbrand.Bridge.finiteConorm (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) a.2) w'
          * (algebraMap L (NumberField.AdeleRing (NumberField.RingOfIntegers L) L) (σ l)).2 w'
        = NumberField.PlaceTransport.transport σ h
          ((M4aHerbrand.Bridge.finiteConorm (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) a.2) w
            * (algebraMap L (NumberField.AdeleRing (NumberField.RingOfIntegers L) L) l).2 w)
    rw [map_mul]
    congr 1
    ·
      have hu : w'.under (NumberField.RingOfIntegers K) = w.under (NumberField.RingOfIntegers K) := by
        rw [← h]; exact NumberField.PlaceTransport.under_smul K L σ w
      rw [M4aHerbrand.Bridge.finiteConorm_apply, M4aHerbrand.Bridge.finiteConorm_apply,
        ← aux_semialgHom_under a.2 w' (w.under (NumberField.RingOfIntegers K)) hu]
      exact (NumberField.PlaceTransport.transport_adicCompletionSemialgHom K L σ ⟨w, rfl⟩ ⟨w', hu⟩ h _).symm
    ·
      show ((σ l : L) : w'.adicCompletion L) = NumberField.PlaceTransport.transport σ h ((l : L) : w.adicCompletion L)
      rw [NumberField.PlaceTransport.transport_coe]
      rfl
