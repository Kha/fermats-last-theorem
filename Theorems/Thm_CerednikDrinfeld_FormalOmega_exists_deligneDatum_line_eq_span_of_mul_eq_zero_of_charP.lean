import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_span_of_mul_eq_zero_of_charP
attribute [-instance] CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀

set_option autoImplicit false

open scoped TensorProduct
p2m_open "LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega~DrinfeldDatum~stalk"

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_span_of_mul_eq_zero_of_charP
    (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ]
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
    (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])
    (c c' : κ) (hcc' : c * c' = 0) (hc : c = 0 ∨ c ^ p ≠ c) (hc' : c' = 0 ∨ c' ^ p ≠ c') :
    ∃ d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) κ,
      d.line (stdFullLattice ℚ_[p]) =
          Submodule.span κ {c ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1} ∧
        d.line (FullLattice.act g (stdFullLattice ℚ_[p])) =
          (Submodule.span κ {(1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + c' ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1}).map
            (actBaseChange κ g (stdFullLattice ℚ_[p])).toLinearMap := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_span_of_mul_eq_zero_of_charP.solution
