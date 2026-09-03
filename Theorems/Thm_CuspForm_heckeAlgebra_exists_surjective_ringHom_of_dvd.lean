import Definitions.Def_CuspForm_HeckeAlgebra
import P2M.Util
import P2M.Sol.S_CuspForm_heckeAlgebra_exists_surjective_ringHom_of_dvd

theorem CuspForm.heckeAlgebra.exists_surjective_ringHom_of_dvd
    (N N' : ℕ) [NeZero N] [NeZero N'] (hNN' : N ∣ N') (k : ℤ) (S : Set ℕ)
    (hN'S : ∀ q : ℕ, q.Prime → q ∣ N' → q ∈ S) :
    ∃ res : CuspForm.heckeAlgebra N' k S →+* CuspForm.heckeAlgebra N k S,
      Function.Surjective res ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN' : ¬ ℓ ∣ N') (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
        res (CuspForm.heckeAlgebra.T hℓ hℓN' hℓS) = CuspForm.heckeAlgebra.T hℓ hℓN hℓS) ∧
      ∀ (t : CuspForm.heckeAlgebra N' k S) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k)
        (g : CuspForm (CongruenceSubgroup.Gamma0 N') k), ⇑g = ⇑f →
        ⇑((res t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) f) =
          ⇑((t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N') k)) g) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeAlgebra_exists_surjective_ringHom_of_dvd.solution
