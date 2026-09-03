import Mathlib
import Definitions.Def_PadicInt_KummerCarrier
import P2M.Util
import P2M.Sol.S_PadicInt_KummerCarrier_bialgebra_axioms

open scoped TensorProduct in
open PadicInt.KummerCarrier in
theorem PadicInt.KummerCarrier.bialgebra_axioms (p : ℕ) [Fact p.Prime] (u : ℤ_[p]ˣ) :
    ((Algebra.TensorProduct.assoc ℤ_[p] ℤ_[p] ℤ_[p]
        (Carrier p u) (Carrier p u) (Carrier p u)).toAlgHom.comp
      ((Algebra.TensorProduct.map (Δ p u) (.id ℤ_[p] (Carrier p u))).comp (Δ p u))
      = (Algebra.TensorProduct.map (.id ℤ_[p] (Carrier p u)) (Δ p u)).comp (Δ p u)) ∧
    ((Algebra.TensorProduct.map (ε p u) (.id ℤ_[p] (Carrier p u))).comp (Δ p u)
      = (Algebra.TensorProduct.lid ℤ_[p] (Carrier p u)).symm) ∧
    ((Algebra.TensorProduct.map (.id ℤ_[p] (Carrier p u)) (ε p u)).comp (Δ p u)
      = (Algebra.TensorProduct.rid ℤ_[p] ℤ_[p] (Carrier p u)).symm) ∧
    (∀ h, (TensorProduct.comm ℤ_[p] (Carrier p u) (Carrier p u)) (Δ p u h) = Δ p u h) := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_KummerCarrier_bialgebra_axioms.solution
