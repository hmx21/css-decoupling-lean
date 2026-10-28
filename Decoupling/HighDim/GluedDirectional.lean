import Decoupling.HighDim.GluedHomotopy
import Decoupling.HighDim.ScalingLattice
import Decoupling.HighDim.KoszulLatticeRestriction

/-!
# The literal directional coarse lattice Z × pZ × Z

Its integer coordinates and index are explicit. The formal y derivative
commutes with its actual scalar restriction in characteristic p, which
turns the already proved homotopy into a retained-ring-linear one.
-/

namespace Decoupling.HighDim.GluedDirectional

open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false

def inclusion (p : ℕ) : Translation 3 →+ Translation 3 where
  toFun a := ![a 0, (p : ℤ) * a 1, a 2]
  map_zero' := by funext i; fin_cases i <;> simp
  map_add' a b := by funext i; fin_cases i <;> simp [mul_add]

def lattice (p : ℕ) : AddSubgroup (Translation 3) := (inclusion p).range

theorem mem_lattice (p : ℕ) (a : Translation 3) : a ∈ lattice p ↔ (p : ℤ) ∣ a 1 := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b 1, rfl⟩
  · rintro ⟨b, hb⟩
    refine ⟨![a 0, b, a 2], ?_⟩
    funext i
    fin_cases i <;> simp [inclusion, hb]

theorem inclusion_injective (p : ℕ) (hp : p ≠ 0) : Function.Injective (inclusion p) := by
  intro a b hab
  funext i
  fin_cases i
  · exact congrFun hab 0
  · have h := congrFun hab 1
    exact mul_left_cancel₀ (by exact_mod_cast hp : (p : ℤ) ≠ 0) h
  · exact congrFun hab 2

def coordinates (p : ℕ) (hp : p ≠ 0) : lattice p ≃+ Translation 3 :=
  (AddMonoidHom.ofInjective (inclusion_injective p hp)).symm

@[simp] theorem coordinates_symm_coe (p : ℕ) (hp : p ≠ 0) (a : Translation 3) :
    ((coordinates p hp).symm a : Translation 3) = inclusion p a := rfl

def residue (p : ℕ) : Translation 3 →+ ZMod p where
  toFun a := a 1
  map_zero' := by simp
  map_add' a b := by simp

theorem residue_surjective (p : ℕ) : Function.Surjective (residue p) := by
  intro a
  obtain ⟨b, hb⟩ := ZMod.intCast_surjective a
  exact ⟨![0, b, 0], hb⟩

theorem lattice_eq_ker (p : ℕ) : lattice p = (residue p).ker := by
  ext a
  rw [mem_lattice]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a 1) p).symm

theorem lattice_index (p : ℕ) : (lattice p).index = p := by
  rw [lattice_eq_ker, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top_of_surjective _ (residue_surjective p)]
  simp

instance lattice_finiteIndex (p : ℕ) [Fact p.Prime] : (lattice p).FiniteIndex where
  index_ne_zero := by rw [lattice_index]; exact (Fact.out : p.Prime).ne_zero

variable (p : ℕ) [Fact p.Prime]

def ringMap : Laurent (ZMod p) 3 →+* Laurent (ZMod p) 3 :=
  KoszulLattice.latticeMap (ZMod p) (inclusion p)

theorem ringMap_eq_coordinateEmbedding : ringMap p =
    ScalingLattice.coordinateEmbedding (ZMod p) (lattice p)
      (coordinates p (Fact.out : p.Prime).ne_zero) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro a
    change ringMap p (constant a) = ScalingLattice.coordinateEmbedding (ZMod p) (lattice p)
      (coordinates p (Fact.out : p.Prime).ne_zero) (constant a)
    simp only [ringMap, KoszulLattice.latticeMap_constant, ScalingLattice.coordinateEmbedding_constant]
  · intro a
    change ringMap p (monomial (ZMod p) a) = ScalingLattice.coordinateEmbedding (ZMod p) (lattice p)
      (coordinates p (Fact.out : p.Prime).ne_zero) (monomial (ZMod p) a)
    simp only [ringMap, KoszulLattice.latticeMap_monomial,
      ScalingLattice.coordinateEmbedding_monomial, coordinates_symm_coe]

/-- Actual retained-scalar linearity; p-th powers have derivative zero. -/
theorem derivative_ringMap_mul (s f : Laurent (ZMod p) 3) :
    laurentDerivative (ZMod p) 1 (ringMap p s * f) =
      ringMap p s * laurentDerivative (ZMod p) 1 f := by
  induction s using AddMonoidAlgebra.induction_on with
  | of a =>
    change laurentDerivative (ZMod p) 1 (ringMap p (monomial (ZMod p) a) * f) =
      ringMap p (monomial (ZMod p) a) * laurentDerivative (ZMod p) 1 f
    rw [ringMap, KoszulLattice.latticeMap_monomial, laurentDerivative_monomial_mul]
    simp [inclusion]
  | add s t hs ht => simp only [map_add, add_mul, hs, ht]
  | smul c s hs =>
    have he : c • s = constant c * s := by
      change c • s = AddMonoidAlgebra.single 0 c * s
      ext a
      simp
    rw [he, (ringMap p).map_mul, show ringMap p (constant c) = constant c from
      KoszulLattice.latticeMap_constant _ _ c]
    change laurentDerivative (ZMod p) 1 (constant c * ringMap p s * f) = _
    rw [mul_assoc]
    have hc (x : Laurent (ZMod p) 3) : constant c * x = c • x := by ext a; simp
    rw [hc, map_smul, hs, hc, smul_mul_assoc]

end
end Decoupling.HighDim.GluedDirectional
