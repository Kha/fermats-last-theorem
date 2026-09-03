import Mathlib
import Definitions.Def_TateCurve_TorsionParametrization
import Definitions.Def_FLTPrelim_GaloisRep
import P2M.Util
import P2M.Sol.S_TateCurve_torsionBy_baseChange_bijective_algebraicClosure_padic
attribute [-simp] WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in
theorem TateCurve.torsionBy_baseChange_bijective_algebraicClosure_padic
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1)
    (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [CharZero K] [IsAlgClosed K] [Algebra ℚ_[p] K]
    (hiso : ∀ x : ℚ_[p], ‖algebraMap ℚ_[p] K x‖ = ‖x‖)
    (ι : AlgebraicClosure ℚ_[p] →ₐ[ℚ_[p]] K) :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    letI : DecidableEq K := Classical.decEq _
    ((TateCurve.curve qT).map (algebraMap ℚ_[p] K) = TateCurve.curve (algebraMap ℚ_[p] K qT)) ∧
    Function.Bijective
      (fun P : Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p =>
        (⟨WeierstrassCurve.Affine.Point.map ι
            (P : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point),
          by
            rw [Submodule.mem_torsionBy_iff, ← AddMonoidHom.map_zsmul,
              (Submodule.mem_torsionBy_iff _ _).mp P.property, AddMonoidHom.map_zero]⟩ :
        Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄K).Point p)) := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_torsionBy_baseChange_bijective_algebraicClosure_padic.solution
