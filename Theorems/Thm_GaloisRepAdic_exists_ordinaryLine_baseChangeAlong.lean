import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_exists_ordinaryLine_baseChangeAlong

set_option autoImplicit false
theorem GaloisRepAdic.exists_ordinaryLine_baseChangeAlong
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (L : Submodule A ρ.V) (hLb : ∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0)
    (hLD : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L)
    (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L) :
    ∃ L' : Submodule B (ρ.baseChangeAlong φ hφ).V,
      (∃ b' : Module.Basis (Fin 2) B (ρ.baseChangeAlong φ hφ).V, L' = B ∙ b' 0) ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L', (ρ.baseChangeAlong φ hφ).ρ σ v ∈ L') ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : (ρ.baseChangeAlong φ hφ).V,
        (ρ.baseChangeAlong φ hφ).ρ σ v - v ∈ L') ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ z : A, (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ L) →
        ∀ v : (ρ.baseChangeAlong φ hφ).V, (ρ.baseChangeAlong φ hφ).ρ σ v - φ z • v ∈ L') ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ z' : B,
        (∀ v : (ρ.baseChangeAlong φ hφ).V, (ρ.baseChangeAlong φ hφ).ρ σ v - z' • v ∈ L') →
        ∃ z : A, (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ L) ∧ φ z = z') := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_exists_ordinaryLine_baseChangeAlong.solution
