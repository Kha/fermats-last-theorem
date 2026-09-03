import Mathlib
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_exists_local_triangular_package_of_ordinaryLine_padicPlace

set_option autoImplicit false
theorem GaloisRepAdic.exists_local_triangular_package_of_ordinaryLine_padicPlace
    {B : Type} [CommRing B] [IsLocalRing B] [Finite B] (p : ℕ) [Fact p.Prime]
    (ρ : GaloisRepAdic B) (hdet : ρ.DetIsCyclotomic p)
    (b : Module.Basis (Fin 2) B ρ.V)
    (hLD : ∀ σ ∈ (padicPlace p).decompositionSubgroup ℚ, ρ.ρ σ (b 0) ∈ B ∙ b 0)
    (hLI : ∀ σ ∈ (padicPlace p).inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ B ∙ b 0)
    (t : B)
    (hsq : ∀ σ ∈ (padicPlace p).decompositionSubgroup ℚ, ∀ z : B,
      (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ B ∙ b 0) → z * z - 1 ∈ Ideal.span {t})
    (hne : ∃ σ ∈ (padicPlace p).decompositionSubgroup ℚ, ∃ z : B,
      (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ B ∙ b 0) ∧ z * z ≠ 1)
    (hIloc : ∀ τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      localGaloisToGlobal p τ ∈ (padicPlace p).inertiaSubgroupIn ℚ)
    (hsur : ∀ σ ∈ (padicPlace p).decompositionSubgroup ℚ,
      ∃ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), ρ.ρ (localGaloisToGlobal p g) = ρ.ρ σ) :
    ∃ (x z : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → Bˣ) (y : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → B)
      (F : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ F ∧
      (∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), ρ.ρ (localGaloisToGlobal p g) (b 0) = (x g : B) • b 0) ∧
      (∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), ρ.ρ (localGaloisToGlobal p g) (b 1) = y g • b 0 + (z g : B) • b 1) ∧
      (∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), x (g * h) = x g * x h) ∧
      (∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), z (g * h) = z g * z h) ∧
      (∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), y (g * h) = (x g : B) * y h + y g * (z h : B)) ∧
      (∀ s : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), localGaloisToGlobal p s ∈ F.fixingSubgroup → x s = 1 ∧ y s = 0 ∧ z s = 1) ∧
      (∀ τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → z τ = 1) ∧
      (∀ (g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (n a : ℕ), (∀ μ : PadicAlgCl p, μ ^ p ^ n = 1 → g μ = μ ^ a) →
        (x g : B) * (z g : B) - (a : B) ∈ Ideal.span {((p ^ n : ℕ) : B)}) ∧
      (∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (z g : B) * (z g : B) - 1 ∈ Ideal.span {t}) ∧
      (∃ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (z g : B) * (z g : B) ≠ 1) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_exists_local_triangular_package_of_ordinaryLine_padicPlace.solution
