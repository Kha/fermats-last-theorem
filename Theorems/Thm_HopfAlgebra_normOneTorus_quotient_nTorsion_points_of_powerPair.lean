import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_normOneTorus_quotient_nTorsion_points_of_powerPair

open scoped TensorProduct in
theorem HopfAlgebra.normOneTorus_quotient_nTorsion_points_of_powerPair
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0)
    (n : ℕ) [Fact n.Prime]
    (δ : AlgebraicClosure K) (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c)
    (B₀ : Type) [CommRing B₀] [Algebra K B₀]
    (u₀ v₀ P Q : B₀)
    (hlift₀ : ∀ (w z : AlgebraicClosure K),
      w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
      ∃! g : B₀ →ₐ[K] AlgebraicClosure K, g u₀ = w ∧ g v₀ = z)
    (hpow : ∀ f : B₀ →ₐ[K] AlgebraicClosure K,
      f P + f Q * δ = (f u₀ + f v₀ * δ) ^ n ∧
      f P - f Q * δ = (f u₀ - f v₀ * δ) ^ n)
    (A : Type) [CommRing A] [Algebra K A]
    (u' v' : A) (π : B₀ →ₐ[K] A)
    (hπu : π u₀ = u') (hπv : π v₀ = v') (hπP : π P = 1) (hπQ : π Q = 0)
    (hfact : ∀ g : B₀ →ₐ[K] AlgebraicClosure K, g P = 1 → g Q = 0 →
      ∃ f : A →ₐ[K] AlgebraicClosure K, f.comp π = g)
    (hgen' : Algebra.adjoin K {u', v'} = ⊤) :
    (∀ f : A →ₐ[K] AlgebraicClosure K, (f u' + f v' * δ) ^ n = 1) ∧
    (∀ (w z : AlgebraicClosure K),
      w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
      (w + z * δ) ^ n = 1 →
      ∃! f : A →ₐ[K] AlgebraicClosure K, f u' = w ∧ f v' = z) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_normOneTorus_quotient_nTorsion_points_of_powerPair.solution
