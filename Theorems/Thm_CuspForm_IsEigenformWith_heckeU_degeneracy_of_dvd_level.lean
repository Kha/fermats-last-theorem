import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import P2M.Util
import P2M.Sol.S_CuspForm_IsEigenformWith_heckeU_degeneracy_of_dvd_level

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.IsEigenformWith.heckeU_degeneracy_of_dvd_level
    (M : ℕ) [NeZero M] (k : ℤ) {L : ℕ} [NeZero L] (hLM : L ∣ M)
    {εL : DirichletCharacter ℂ L} {g : CuspForm (CongruenceSubgroup.Gamma1 L) k}
    (hg : CuspForm.IsEigenformWith εL g)
    (G : ℕ → CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (hG : ∀ d : ℕ, d ∣ M / L → ∀ τ : UpperHalfPlane, G d τ = g (ModularForm.heckeDiagMatrix d • τ))
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) {d : ℕ} (hd : d ∣ M / L) :
    (q ∣ d → ModularForm.heckeU k q ⇑(G d) = ⇑(G (d / q))) ∧
    (¬ q ∣ d → q ∣ L → ModularForm.heckeU k q ⇑(G d) = ModularFormClass.qCoeff g q • ⇑(G d)) ∧
    (¬ q ∣ d → ¬ q ∣ L →
      ModularForm.heckeU k q ⇑(G d) =
        ModularFormClass.qCoeff g q • ⇑(G d) -
          (εL (q : ZMod L) * (q : ℂ) ^ (k - 1)) • ⇑(G (d * q))) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsEigenformWith_heckeU_degeneracy_of_dvd_level.solution
