import Mathlib
import P2M.Util
namespace P2MW.S_TransportGlue_exists_pairing_of_linearEquiv
set_option autoImplicit false

namespace TransportGlue

theorem exists_pairing_of_linearEquiv'
    {𝒪 A A' M N : Type} [CommRing 𝒪] [CommRing A] [CommRing A'] [Algebra 𝒪 A] [Algebra 𝒪 A']
    [AddCommGroup M] [Module 𝒪 M] [Module A M] [IsScalarTower 𝒪 A M]
    [AddCommGroup N] [Module 𝒪 N] [Module A' N] [IsScalarTower 𝒪 A' N]
    (s : M ≃ₗ[𝒪] N) (φ : A → A') (hφ : Function.Surjective φ) (hs : ∀ (a : A) (m : M), s (a • m) = φ a • s m)
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (hB : ∀ (a : A) (m n : M), B (a • m) n = B m (a • n)) (hBbij : Function.Bijective B) :
    ∃ B' : N →ₗ[𝒪] N →ₗ[𝒪] 𝒪, (∀ n n' : N, B' n n' = B (s.symm n) (s.symm n')) ∧
      (∀ (a' : A') (n n' : N), B' (a' • n) n' = B' n (a' • n')) ∧ Function.Bijective B' := by
  let B' : N →ₗ[𝒪] N →ₗ[𝒪] 𝒪 := (B.comp (s.symm : N →ₗ[𝒪] M)).compl₂ (s.symm : N →ₗ[𝒪] M)
  have hB' : ∀ n n' : N, B' n n' = B (s.symm n) (s.symm n') := fun _ _ => rfl
  refine ⟨B', hB', ?_, ?_⟩
  · intro a' n n'
    obtain ⟨a, rfl⟩ := hφ a'
    have h1 : s.symm (φ a • n) = a • s.symm n := by
      apply s.injective; rw [hs, s.apply_symm_apply, s.apply_symm_apply]
    have h2 : s.symm (φ a • n') = a • s.symm n' := by
      apply s.injective; rw [hs, s.apply_symm_apply, s.apply_symm_apply]
    rw [hB', hB', h1, h2, hB]
  ·
    have hfac : (B' : N → (N →ₗ[𝒪] 𝒪)) = (fun f : M →ₗ[𝒪] 𝒪 => f.comp (s.symm : N →ₗ[𝒪] M)) ∘ B ∘ s.symm := by
      funext n; apply LinearMap.ext; intro n'; rfl
    rw [hfac]
    refine (Function.Bijective.comp ?_ (hBbij.comp s.symm.bijective))
    refine Function.bijective_iff_has_inverse.mpr ⟨fun g : N →ₗ[𝒪] 𝒪 => g.comp (s : M →ₗ[𝒪] N), fun f => ?_, fun g => ?_⟩
    · apply LinearMap.ext; intro m; simp
    · apply LinearMap.ext; intro n; simp

end TransportGlue

theorem solution
    {𝒪 A A' M N : Type} [CommRing 𝒪] [CommRing A] [CommRing A'] [Algebra 𝒪 A] [Algebra 𝒪 A']
    [AddCommGroup M] [Module 𝒪 M] [Module A M] [IsScalarTower 𝒪 A M]
    [AddCommGroup N] [Module 𝒪 N] [Module A' N] [IsScalarTower 𝒪 A' N]
    (s : M ≃ₗ[𝒪] N) (φ : A → A') (hφ : Function.Surjective φ) (hs : ∀ (a : A) (m : M), s (a • m) = φ a • s m)
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (hB : ∀ (a : A) (m n : M), B (a • m) n = B m (a • n)) (hBbij : Function.Bijective B) :
    ∃ B' : N →ₗ[𝒪] N →ₗ[𝒪] 𝒪, (∀ n n' : N, B' n n' = B (s.symm n) (s.symm n')) ∧
      (∀ (a' : A') (n n' : N), B' (a' • n) n' = B' n (a' • n')) ∧ Function.Bijective B' :=
  TransportGlue.exists_pairing_of_linearEquiv' s φ hφ hs B hB hBbij
