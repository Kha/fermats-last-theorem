import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_forall_surjective_of_forall_projective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct AlgebraicGeometry.HilbertFunctor

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_span_of_forall_surjective_of_forall_projective
    (n m : ℕ) (A : Type u) [CommRing A] (h : ℕ → ℕ)
    (hlow : ∀ d : ℕ, d < m → h d = Nat.choose (n + d) n)
    (N : ℕ → Type u) [∀ d, AddCommGroup (N d)] [∀ d, Module A (N d)]
    (Θ : ∀ d : ℕ, ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A d) →ₗ[A] N d)
    (hfin : ∀ d : ℕ, m ≤ d → Module.Finite A (N d))
    (hproj : ∀ d : ℕ, m ≤ d → Module.Projective A (N d))
    (hrank : ∀ d : ℕ, m ≤ d → ∀ 𝔮 : PrimeSpectrum A, Module.rankAtStalk (N d) 𝔮 = h d)
    (hsurj : ∀ d : ℕ, m ≤ d → Function.Surjective (Θ d))
    (hmul : ∀ d : ℕ, m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d)
      (e : ℕ) (G : MvPolynomial (Fin (n + 1)) A) (hG : G.IsHomogeneous e),
      Θ d ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ = 0 →
        Θ (e + d) ⟨G * F, (MvPolynomial.mem_homogeneousSubmodule (e + d) (G * F)).mpr (hG.mul hF)⟩ = 0) :
    ∃ p : Point A n h,
      p.I = Ideal.span {F : MvPolynomial (Fin (n + 1)) A | ∃ (d : ℕ) (hF : F.IsHomogeneous d), m ≤ d ∧
        Θ d ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ = 0} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_forall_surjective_of_forall_projective.solution
