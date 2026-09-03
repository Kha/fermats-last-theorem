import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_finrank_fieldRange_le_of_adjoin_pair_eq_top

theorem IntermediateField.finrank_fieldRange_le_of_adjoin_pair_eq_top {K L : Type*} [Field K] [Field L] [Algebra K L] (X Y : L) (hgen : IntermediateField.adjoin K {X, Y} = ⊤) (A B : L) (hA : A ∈ IntermediateField.adjoin K {X}) (hB : B ∈ IntermediateField.adjoin K {X}) (hY : Y ^ 2 + A * Y + B = 0) (μ ι : L →ₐ[K] L) (hιX : ι X = X) (hιY : ι Y ^ 2 + A * ι Y + B = 0) (hιμ : ι (μ Y) ≠ μ Y) (Φ Ψ : Polynomial K) {d : ℕ} (hd : 0 < d) (hroot : Polynomial.aeval X Φ = μ X * Polynomial.aeval X Ψ) (hdeg : ∀ (M : IntermediateField K L) (c : M), (Φ.map (algebraMap K M) - Polynomial.C c * Ψ.map (algebraMap K M)).natDegree = d) : FiniteDimensional μ.fieldRange L ∧ Module.finrank μ.fieldRange L ≤ d := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_finrank_fieldRange_le_of_adjoin_pair_eq_top.solution
