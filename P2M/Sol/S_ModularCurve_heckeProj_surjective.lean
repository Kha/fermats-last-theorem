import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_ModularCurve_HeckeProj
import P2M.Util
namespace P2MW.S_ModularCurve_heckeProj_surjective
p2m_open "ModularCurve P2MW.S_ModularCurve_heckeProj_surjective.ModularCurve"

namespace S09RC

private theorem exists_heckeProj_coe_eq (N : ℕ) [NeZero N]
    {x : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)}
    (hx : x ∈ Algebra.adjoin ℤ (CuspForm.heckeGenerators N 2 ∅)) :
    ∃ t : HeckeAlg,
      ((heckeProj N t : CuspForm.heckeAlgebra N 2 ∅) :
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) = x := by
  induction hx using Algebra.adjoin_induction with
  | mem T hT =>
    rcases hT with ⟨ℓ, hℓ, hℓN, -, rfl⟩ | ⟨q, hqN, hq, -, rfl⟩
    · exact ⟨heckeGen ⟨ℓ, hℓ⟩, by
        rw [heckeProj_heckeGen_of_not_dvd ⟨ℓ, hℓ⟩ hℓN, CuspForm.heckeAlgebra.coe_T]⟩
    · exact ⟨heckeGen ⟨q, hq⟩, by
        rw [heckeProj_heckeGen_of_dvd ⟨q, hq⟩ hqN, CuspForm.heckeAlgebra.coe_U]⟩
  | algebraMap r => exact ⟨MvPolynomial.C r, by rw [heckeProj_C, Subalgebra.coe_algebraMap]⟩
  | add a b _ _ iha ihb =>
    obtain ⟨ta, hta⟩ := iha
    obtain ⟨tb, htb⟩ := ihb
    exact ⟨ta + tb, by rw [map_add, Subalgebra.coe_add, hta, htb]⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨ta, hta⟩ := iha
    obtain ⟨tb, htb⟩ := ihb
    exact ⟨ta * tb, by rw [map_mul, Subalgebra.coe_mul, hta, htb]⟩

end S09RC

namespace ModularCurve p2m_export "ModularCurve" "HeckeAlg heckeGen heckeProj heckeProj_heckeGen_of_not_dvd heckeProj_heckeGen_of_dvd heckeProj_C" end ModularCurve
p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.heckeProj_surjective (p : ℕ) [NeZero p] : Function.Surjective (heckeProj p) := by
  rintro ⟨x, hx⟩
  obtain ⟨t, ht⟩ := S09RC.exists_heckeProj_coe_eq p hx
  exact ⟨t, Subtype.ext ht⟩

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_heckeProj_surjective.ModularCurve in
theorem solution : ∀ (p : ℕ) [NeZero p], Function.Surjective (heckeProj p) :=
  @ModularCurve.heckeProj_surjective
