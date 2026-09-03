import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_bijective_transpose_mulVec_of_adjoin_intCast

set_option autoImplicit false

theorem Matrix.exists_bijective_transpose_mulVec_of_adjoin_intCast
    {ι : Type*} (n d : ℕ) (M : ι → Matrix (Fin n) (Fin n) ℤ)
    (hcomm : ∀ i j, M i * M j = M j * M i)
    (hfree : ∃ v : Fin d → (Fin n → ℂ), Function.Bijective
      (fun c : Fin d → ↥(Algebra.adjoin ℂ (Set.range fun i => (M i).map (Int.cast : ℤ → ℂ))) =>
        ∑ k, ((c k : Matrix (Fin n) (Fin n) ℂ).mulVec (v k))))
    (hmult : ∀ χ : ↥(Algebra.adjoin ℂ (Set.range fun i => (M i).map (Int.cast : ℤ → ℂ))) →ₐ[ℂ] ℂ,
      Module.finrank ℂ ↥(⨅ a : ↥(Algebra.adjoin ℂ (Set.range fun i => (M i).map (Int.cast : ℤ → ℂ))),
        Module.End.eigenspace (Matrix.toLin' (a : Matrix (Fin n) (Fin n) ℂ)) (χ a)) = d)
    (K : Type*) [Field K] [CharZero K] :
    ∃ w : Fin d → (Fin n → K), Function.Bijective
      (fun c : Fin d → ↥(Algebra.adjoin K (Set.range fun i => ((M i).transpose).map (Int.cast : ℤ → K))) =>
        ∑ k, ((c k : Matrix (Fin n) (Fin n) K).mulVec (w k))) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_bijective_transpose_mulVec_of_adjoin_intCast.solution
