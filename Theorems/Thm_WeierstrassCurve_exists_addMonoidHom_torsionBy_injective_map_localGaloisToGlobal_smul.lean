import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_addMonoidHom_torsionBy_injective_map_localGaloisToGlobal_smul

open scoped WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_addMonoidHom_torsionBy_injective_map_localGaloisToGlobal_smul
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (n : ℕ) :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ ψ : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point n →+
          Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point n,
      Function.Injective ψ ∧
      ∀ (τ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
        (P : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point n),
        ψ ((localGaloisToGlobal p τ) • P) = τ • ψ P := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_addMonoidHom_torsionBy_injective_map_localGaloisToGlobal_smul.solution
