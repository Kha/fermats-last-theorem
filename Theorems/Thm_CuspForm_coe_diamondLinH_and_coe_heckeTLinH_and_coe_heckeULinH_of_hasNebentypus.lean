import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import P2M.Util
import P2M.Sol.S_CuspForm_coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (ε : DirichletCharacter ℂ M)
    (f : CuspForm (CohCarrier.GammaH M H) k) (g : CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (hfg : (⇑f : UpperHalfPlane → ℂ) = ⇑g) (hg : CuspForm.HasNebentypus ε g) :
    (∀ d : (ZMod M)ˣ, (⇑(CuspForm.diamondLinH k d f) : UpperHalfPlane → ℂ) = ε (d : ZMod M) • ⇑g) ∧
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M),
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      (⇑(CuspForm.heckeTLinH k hℓ hℓM f) : UpperHalfPlane → ℂ) =
        ModularForm.heckeU k ℓ ⇑g + ε (ℓ : ZMod M) • ((⇑g) ∣[k] ModularForm.heckeDiagMatrix ℓ)) ∧
    (∀ (q : ℕ), q.Prime → q ∣ M →
      (⇑(CuspForm.heckeULinH k q f) : UpperHalfPlane → ℂ) = ModularForm.heckeU k q ⇑g) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus.solution
