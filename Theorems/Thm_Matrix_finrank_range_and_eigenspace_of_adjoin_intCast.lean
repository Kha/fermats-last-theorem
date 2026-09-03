import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Analysis.Complex.Basic
import P2M.Util
import P2M.Sol.S_Matrix_finrank_range_and_eigenspace_of_adjoin_intCast

set_option autoImplicit false

theorem Matrix.finrank_range_and_eigenspace_of_adjoin_intCast
    {ι : Type*} (n d : ℕ) (M : ι → Matrix (Fin n) (Fin n) ℤ)
    (hfree : ∃ v : Fin d → (Fin n → ℂ), Function.Bijective
      (fun c : Fin d → ↥(Algebra.adjoin ℂ (Set.range fun i => (M i).map (Int.cast : ℤ → ℂ))) =>
        ∑ k, ((c k : Matrix (Fin n) (Fin n) ℂ).mulVec (v k))))
    (hmult : ∀ χ : ↥(Algebra.adjoin ℂ (Set.range fun i => (M i).map (Int.cast : ℤ → ℂ))) →ₐ[ℂ] ℂ,
      Module.finrank ℂ ↥(⨅ a : ↥(Algebra.adjoin ℂ (Set.range fun i => (M i).map (Int.cast : ℤ → ℂ))),
        Module.End.eigenspace (Matrix.toLin' (a : Matrix (Fin n) (Fin n) ℂ)) (χ a)) = d)
    (𝒪 : Type*) [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪] [CharZero 𝒪] :
    (∀ ε ∈ Algebra.adjoin 𝒪 (Set.range fun i => (M i).map (Int.cast : ℤ → 𝒪)),
      IsIdempotentElem ε →
        Module.finrank 𝒪 ↥(LinearMap.range (Matrix.toLin' ε)) =
          d * Module.finrank 𝒪 ↥(LinearMap.range (LinearMap.mulLeft 𝒪 ε ∘ₗ
            (Algebra.adjoin 𝒪 (Set.range fun i => (M i).map (Int.cast : ℤ → 𝒪))).val.toLinearMap))) ∧
    ∀ lam : ↥(Algebra.adjoin 𝒪 (Set.range fun i => (M i).map (Int.cast : ℤ → 𝒪))) →ₐ[𝒪] 𝒪,
      Module.finrank 𝒪 ↥(⨅ a : ↥(Algebra.adjoin 𝒪 (Set.range fun i => (M i).map (Int.cast : ℤ → 𝒪))),
        Module.End.eigenspace (Matrix.toLin' (a : Matrix (Fin n) (Fin n) 𝒪)) (lam a)) = d := by p2m_exact_reverting @_root_.P2MW.S_Matrix_finrank_range_and_eigenspace_of_adjoin_intCast.solution
