import Mathlib
import Definitions.Def_IharaLemma_IdempotentSplitting
import P2M.Util
import P2M.Sol.S_GaloisLattice_exists_adaptedBasis_cornerSubmodule_of_involution_of_similitudePairing

set_option autoImplicit false

theorem GaloisLattice.exists_adaptedBasis_cornerSubmodule_of_involution_of_similitudePairing
    (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T]
    [Module.Free ℤ_[p] T] {ι₀ : Type} (A : ι₀ → Module.End ℤ_[p] T)
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 T] [IsScalarTower ℤ_[p] 𝕋 T]
    (hfaith : ∀ t : 𝕋, (∀ x : T, t • x = 0) → t = 0)
    (op : ι₀ → 𝕋) (hop : ∀ (g : ι₀) (x : T), op g • x = A g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (S' : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin S'.n)
    (P0 : Submodule 𝕋 T) (s0 t1 : Module.End ℤ_[p] T) (u : ℤ_[p]) (h2 : IsUnit (2 : ℤ_[p]))
    (hs0 : ∀ (t : 𝕋) (x : T), s0 (t • x) = t • s0 x) (ht1 : ∀ (t : 𝕋) (x : T), t1 (t • x) = t • t1 x)
    (hP0 : ∀ x : T, x ∈ P0 ↔ x ∈ IharaLemma.cornerSubmodule (M := T) (S'.e i₀) ∧ s0 x = -x)
    (hsq : ∀ x ∈ IharaLemma.cornerSubmodule (M := T) (S'.e i₀), s0 (s0 x) = x)
    (ht1P0 : ∀ x ∈ P0, t1 x = u • x)
    (ht1unr : ∀ x ∈ IharaLemma.cornerSubmodule (M := T) (S'.e i₀), t1 x - x ∈ P0)
    (b : Module.Basis (Fin 2)
      ↥(Algebra.adjoin ℚ_[p] (Set.range fun g : ι₀ => (A g).baseChange ℚ_[p]))
      (TensorProduct ℤ_[p] ℚ_[p] T))
    (B : TensorProduct ℤ_[p] ℚ_[p] T →ₗ[ℚ_[p]] TensorProduct ℤ_[p] ℚ_[p] T →ₗ[ℚ_[p]] ℚ_[p])
    (hBnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hBself : ∀ (g : ι₀) (x y : TensorProduct ℤ_[p] ℚ_[p] T),
      B ((A g).baseChange ℚ_[p] x) y = B x ((A g).baseChange ℚ_[p] y))
    (hBsim : ∀ x y : TensorProduct ℤ_[p] ℚ_[p] T,
      B (t1.baseChange ℚ_[p] x) (t1.baseChange ℚ_[p] y) = ((u : ℤ_[p]) : ℚ_[p]) * B x y)
    (hu : ((u : ℤ_[p]) : ℚ_[p]) * (((u : ℤ_[p]) : ℚ_[p]) - 1) ≠ 0) :
    ∃ (x₀ y : T) (N : ℕ), x₀ ∈ P0 ∧ y ∈ IharaLemma.cornerSubmodule (M := T) (S'.e i₀) ∧ s0 y = y ∧
      (∀ a b : S'.CornerRing i₀,
        ((a : S'.CornerRing i₀) : 𝕋) • x₀ + ((b : S'.CornerRing i₀) : 𝕋) • y = 0 → a = 0 ∧ b = 0) ∧
      (∀ z ∈ IharaLemma.cornerSubmodule (M := T) (S'.e i₀), ∃ a b : S'.CornerRing i₀,
        ((p : ℤ_[p]) ^ N) • z = ((a : S'.CornerRing i₀) : 𝕋) • x₀ + ((b : S'.CornerRing i₀) : 𝕋) • y) ∧
      (∀ z ∈ P0, ∃ a : S'.CornerRing i₀, ((p : ℤ_[p]) ^ N) • z = ((a : S'.CornerRing i₀) : 𝕋) • x₀) ∧
      (∀ z ∈ IharaLemma.cornerSubmodule (M := T) (S'.e i₀), s0 z = z →
        ∃ b : S'.CornerRing i₀, ((p : ℤ_[p]) ^ N) • z = ((b : S'.CornerRing i₀) : 𝕋) • y) := by p2m_exact_reverting @_root_.P2MW.S_GaloisLattice_exists_adaptedBasis_cornerSubmodule_of_involution_of_similitudePairing.solution
