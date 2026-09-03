import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_iff_of_line_eq_span_node

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.isQuadrupleOf_iff_of_line_eq_span_node
    (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ]
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
    (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])
    (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
    (hd0 : d.line (stdFullLattice ℚ_[p]) =
      Submodule.span κ {(0 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1})
    (hd1 : d.line (FullLattice.act g (stdFullLattice ℚ_[p])) =
      (Submodule.span κ {(1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (0 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1}).map
        (actBaseChange κ g (stdFullLattice ℚ_[p])).toLinearMap)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) κ) (x : PrimeSpectrum κ) :
    Q.IsQuadrupleOf d ↔
      ∃ (h₀ : Q.N₀ x = (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1)
        (h₁ : Q.N₁ x = (FullLattice.act (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
          (FullLattice.act g (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]))).1),
        LinearMap.ker (Q.u₀ x) = Submodule.span (locRing κ x)
          {transportEquiv (locRing κ x) (M₁ := stdFullLattice ℚ_[p]) (M₂ := Q.L₀ x) h₀.symm
            ((0 : locRing κ x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : locRing κ x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1)} ∧
        LinearMap.ker (Q.u₁ x) = Submodule.span (locRing κ x)
          {transportEquiv (locRing κ x)
              (M₁ := FullLattice.act (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
                (FullLattice.act g (stdFullLattice ℚ_[p]))) (M₂ := Q.L₁ x) h₁.symm
            (actBaseChange (locRing κ x) (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
              (FullLattice.act g (stdFullLattice ℚ_[p]))
              (actBaseChange (locRing κ x) g (stdFullLattice ℚ_[p])
                ((1 : locRing κ x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (0 : locRing κ x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1)))} := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_iff_of_line_eq_span_node.solution
