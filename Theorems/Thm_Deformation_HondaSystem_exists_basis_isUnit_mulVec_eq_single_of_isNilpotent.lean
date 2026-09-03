import Mathlib
import P2M.Util
import P2M.Sol.S_Deformation_HondaSystem_exists_basis_isUnit_mulVec_eq_single_of_isNilpotent

universe u v

theorem Deformation.HondaSystem.exists_basis_isUnit_mulVec_eq_single_of_isNilpotent
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (L : Type v) [AddCommGroup L] [Module 𝓞 L] [Module.Free 𝓞 L] [Module.Finite 𝓞 L]
    (hrank : Module.finrank 𝓞 L = d)
    (lam₀ lam₁ : L →ₗ[𝓞] (Fin d → ZMod p)) (hsurj : Function.Surjective lam₀)
    (hkerlam : ∀ m : L, lam₀ m = 0 → m ∈ Ideal.span {(p : 𝓞)} • (⊤ : Submodule 𝓞 L))
    (C : Matrix (Fin d) (Fin d) (ZMod p)) (hC : IsNilpotent C) (hlam₁ : ∀ m, lam₁ m = C.mulVec (lam₀ m)) :
    ∃ (b : Module.Basis (Fin d) 𝓞 L) (P : Matrix (Fin d) (Fin d) 𝓞), IsUnit P ∧
      (∀ i, (P.map (algebraMap 𝓞 (ZMod p))).mulVec (lam₀ (b i)) = Pi.single i 1) ∧
      (∀ i j : Fin d, j ≤ i → (P.map (algebraMap 𝓞 (ZMod p))).mulVec (lam₁ (b i)) j = 0) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_HondaSystem_exists_basis_isUnit_mulVec_eq_single_of_isNilpotent.solution
