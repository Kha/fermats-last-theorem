import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_counit_apply_eq_zero_of_comul_eq_adicEval

open scoped TensorProduct
open MvPowerSeries

universe u v

theorem MvFormalGroup.counit_apply_eq_zero_of_comul_eq_adicEval
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞)
    (R : Type v) [CommRing R] [Bialgebra 𝓞 R]
    [IsAdicComplete (Ideal.span {(p : R)}) R] [IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R)]
    (x : Fin d → R) (hx : ∀ i, x i ∈ (Ideal.span {(p : R)}).radical)
    (hΔ : ∀ i, Coalgebra.comul (R := 𝓞) (x i) =
      MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)})
        (Sum.elim (fun j => x j ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] x j))
        (F.toPowerSeries i)) :
    ∀ i, Coalgebra.counit (R := 𝓞) (x i) = 0 := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_counit_apply_eq_zero_of_comul_eq_adicEval.solution
