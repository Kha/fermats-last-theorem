import Mathlib
import P2M.Util
import P2M.Sol.S_TransportGlue_exists_pairing_of_linearEquiv
set_option autoImplicit false

theorem TransportGlue.exists_pairing_of_linearEquiv
    {𝒪 A A' M N : Type} [CommRing 𝒪] [CommRing A] [CommRing A'] [Algebra 𝒪 A] [Algebra 𝒪 A']
    [AddCommGroup M] [Module 𝒪 M] [Module A M] [IsScalarTower 𝒪 A M]
    [AddCommGroup N] [Module 𝒪 N] [Module A' N] [IsScalarTower 𝒪 A' N]
    (s : M ≃ₗ[𝒪] N) (φ : A → A') (hφ : Function.Surjective φ) (hs : ∀ (a : A) (m : M), s (a • m) = φ a • s m)
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (hB : ∀ (a : A) (m n : M), B (a • m) n = B m (a • n)) (hBbij : Function.Bijective B) :
    ∃ B' : N →ₗ[𝒪] N →ₗ[𝒪] 𝒪, (∀ n n' : N, B' n n' = B (s.symm n) (s.symm n')) ∧
      (∀ (a' : A') (n n' : N), B' (a' • n) n' = B' n (a' • n')) ∧ Function.Bijective B' := by p2m_exact_reverting @_root_.P2MW.S_TransportGlue_exists_pairing_of_linearEquiv.solution
