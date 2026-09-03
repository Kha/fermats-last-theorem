import Mathlib
import Definitions.Def_PadicInt_KummerCarrier
import P2M.Util
import P2M.Sol.S_PadicInt_KummerCarrier_comul_coassoc

open scoped TensorProduct in
open PadicInt.KummerCarrier in
theorem PadicInt.KummerCarrier.comul_coassoc (p : ℕ) [Fact p.Prime] (u : ℤ_[p]ˣ) :
    (Algebra.TensorProduct.assoc ℤ_[p] ℤ_[p] ℤ_[p]
        (Carrier p u) (Carrier p u) (Carrier p u)).toAlgHom.comp
      ((Algebra.TensorProduct.map (Δ p u) (.id ℤ_[p] (Carrier p u))).comp (Δ p u))
      = (Algebra.TensorProduct.map (.id ℤ_[p] (Carrier p u)) (Δ p u)).comp (Δ p u) := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_KummerCarrier_comul_coassoc.solution
