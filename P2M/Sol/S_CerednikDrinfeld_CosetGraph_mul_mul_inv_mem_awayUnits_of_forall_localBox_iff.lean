import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_CosetGraph_mul_mul_inv_mem_awayUnits_of_forall_localBox_iff

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CerednikDrinfeld CerednikDrinfeld.Omega ValuationSubring QuaternionAlgebra IsDedekindDomain

theorem solution
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) (w : (ℍ[ℚ, a, b])ˣ)
    (hw : ∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v → ∀ x : CosetGraph.Loc a b u,
      ((((CosetGraph.toLoc u w)⁻¹ : (CosetGraph.Loc a b u)ˣ) : CosetGraph.Loc a b u) * x *
          ((CosetGraph.toLoc u w : (CosetGraph.Loc a b u)ˣ) : CosetGraph.Loc a b u) ∈ Submodule.localBox R u ↔
        x ∈ Submodule.localBox R u))
    (x : (ℍ[ℚ, a, b])ˣ) (hx : x ∈ CerednikDrinfeld.CosetGraph.awayUnits R v) :
    w * x * w⁻¹ ∈ CerednikDrinfeld.CosetGraph.awayUnits R v := by
  classical

  simp only [CerednikDrinfeld.CosetGraph.awayUnits, Subgroup.mem_iInf, Subgroup.mem_comap] at hx ⊢
  intro u hu
  have hxu := hx u hu

  set c : (CosetGraph.Loc a b u)ˣ := CosetGraph.toLoc u w with hc
  have hconj : ∀ y : (CosetGraph.Loc a b u)ˣ, y ∈ Submodule.localBoxUnits R u →
      c * y * c⁻¹ ∈ Submodule.localBoxUnits R u := by
    intro y hy
    obtain ⟨hy₁, hy₂⟩ := hy
    refine ⟨(hw u hu _).mp ?_, (hw u hu _).mp ?_⟩
    · have : ((c⁻¹ : (CosetGraph.Loc a b u)ˣ) : CosetGraph.Loc a b u) * ((c * y * c⁻¹ : (CosetGraph.Loc a b u)ˣ) :
          CosetGraph.Loc a b u) * (c : CosetGraph.Loc a b u) = (y : CosetGraph.Loc a b u) := by
        push_cast
        rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
      rw [this]; exact hy₁
    · have : ((c⁻¹ : (CosetGraph.Loc a b u)ˣ) : CosetGraph.Loc a b u) *
          (((c * y * c⁻¹)⁻¹ : (CosetGraph.Loc a b u)ˣ) : CosetGraph.Loc a b u) * (c : CosetGraph.Loc a b u) =
          ((y⁻¹ : (CosetGraph.Loc a b u)ˣ) : CosetGraph.Loc a b u) := by
        rw [mul_inv_rev, mul_inv_rev, inv_inv]
        push_cast
        rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
      rw [this]; exact hy₂

  have hle : (Subgroup.closure (Submodule.localBoxUnits R u)).map (MulAut.conj c).toMonoidHom ≤
      Subgroup.closure (Submodule.localBoxUnits R u) := by
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hconj y hy
  have hmem : (MulAut.conj c).toMonoidHom (CosetGraph.toLoc u x) ∈
      (Subgroup.closure (Submodule.localBoxUnits R u)).map (MulAut.conj c).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hxu
  have := hle hmem
  simpa only [map_mul, map_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hc] using this
