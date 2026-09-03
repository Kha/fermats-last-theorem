import Mathlib
import P2M.Util
namespace P2MW.S_IsLocalRing_residueMap_comp_algHom_eq_of_surjective

set_option autoImplicit false

open IsLocalRing

theorem solution
    (Λ : Type) [CommRing Λ] (k : Type) [Field k] (res₀ : Λ →+* k) (hres₀ : Function.Surjective res₀)
    (A : Type) [CommRing A] [IsLocalRing A] [Algebra Λ A]
    (rA : A →+* k) (hkerA : RingHom.ker rA = maximalIdeal A) (hrA : ∀ w : Λ, rA (algebraMap Λ A w) = res₀ w)
    (B : Type) [CommRing B] [Algebra Λ B] (rB : B →+* k) (hrB : ∀ w : Λ, rB (algebraMap Λ B w) = res₀ w)
    (Φ : A →ₐ[Λ] B) : ∀ a : A, rB (Φ a) = rA a := by
  intro a
  let r' : A →+* k := rB.comp Φ.toRingHom
  have hr'w : ∀ w, r' (algebraMap Λ A w) = res₀ w := fun w => by
    show rB (Φ (algebraMap Λ A w)) = res₀ w
    rw [Φ.commutes, hrB]
  have hsurj : Function.Surjective r' := fun x => by
    obtain ⟨w, hw⟩ := hres₀ x
    exact ⟨algebraMap Λ A w, (hr'w w).trans hw⟩
  have hker' : RingHom.ker r' = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective r' hsurj)
  obtain ⟨w, hw⟩ := hres₀ (rA a)
  have hm : a - algebraMap Λ A w ∈ maximalIdeal A := by
    rw [← hkerA, RingHom.mem_ker, map_sub, hrA, hw, sub_self]
  have hm' : a - algebraMap Λ A w ∈ RingHom.ker r' := by rw [hker']; exact hm
  rw [RingHom.mem_ker, map_sub, hr'w, sub_eq_zero] at hm'
  show r' a = rA a
  rw [hm', hw]
