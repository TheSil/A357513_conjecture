import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# An odd-exponent family of prime-power congruences

For an integer m, let u m n be the reduced numerator of
sum k = 1, ..., n, k ^ (-(2*m+1)) * choose(n,k)^2 * choose(n+k,k)^2.
The file proves that p ^ 4 ∣ u m (p - 1) for every prime outside
the explicit exceptional set exceptionalPrimes m.

The proof formalizes the exact binomial-product expansion, generalized
harmonic pairing, finite-field power-sum obstruction, and passage from the
modular sum to the reduced rational numerator.
-/

namespace OddExponentCongruence

open scoped BigOperators
lemma mem_Icc_coprime_prime {p k : ℕ} [Fact p.Prime]
    (hk : k ∈ Finset.Icc 1 (p - 1)) :
    k.Coprime p := by
  have hp : p.Prime := Fact.out
  rcases Finset.mem_Icc.mp hk with ⟨hk1, hkle⟩
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)

/-- Reflection of the nonzero representatives by \`k ↦ p - k\`. -/
def reflectionEquiv (p : ℕ) [Fact p.Prime] :
    {k : ℕ // k ∈ Finset.Icc 1 (p - 1)} ≃
      {k : ℕ // k ∈ Finset.Icc 1 (p - 1)} where
  toFun k := ⟨p - k.1, by
    have hp : p.Prime := Fact.out
    rcases Finset.mem_Icc.mp k.2 with ⟨hk1, hkle⟩
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  invFun k := ⟨p - k.1, by
    have hp : p.Prime := Fact.out
    rcases Finset.mem_Icc.mp k.2 with ⟨hk1, hkle⟩
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  left_inv k := by
    apply Subtype.ext
    rcases Finset.mem_Icc.mp k.2 with ⟨hk1, hkle⟩
    have hp : p.Prime := Fact.out
    simp only
    omega
  right_inv k := by
    apply Subtype.ext
    rcases Finset.mem_Icc.mp k.2 with ⟨hk1, hkle⟩
    have hp : p.Prime := Fact.out
    simp only
    omega

def residueUnitEquiv (p : ℕ) [Fact p.Prime] :
    {k : ℕ // k ∈ Finset.Icc 1 (p - 1)} ≃ (ZMod p)ˣ where
  toFun k := ZMod.unitOfCoprime k.1 (mem_Icc_coprime_prime k.2)
  invFun u :=
    ⟨(u : ZMod p).val, by
      have hlt := ZMod.val_lt (u : ZMod p)
      have hne : (u : ZMod p).val ≠ 0 := by
        intro h
        exact u.ne_zero ((ZMod.val_eq_zero _).mp h)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  left_inv k := by
    apply Subtype.ext
    have hklt : k.1 < p := by
      rcases Finset.mem_Icc.mp k.2 with ⟨hk1, hkle⟩
      have hp : p.Prime := Fact.out
      omega
    simp only
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt hklt]
  right_inv u := by
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val]

/-- Rewrite the representative-indexed harmonic sum as a sum over units. -/
def correctionProd (p k m : ℕ) : ZMod m :=
  ∏ j ∈ Finset.Ico 1 k,
    (1 - (p : ZMod m) ^ 2 * ((j : ZMod m)⁻¹) ^ 2)

/-- The closed product occurring in the paper proof. -/
def binomialClosed (p k m : ℕ) : ZMod m :=
  (-1 : ZMod m) ^ k * (p : ZMod m) * (k : ZMod m)⁻¹ *
    (1 - (p : ZMod m) * (k : ZMod m)⁻¹) * correctionProd p k m

/-- The product of the two binomial coefficients, reduced modulo \`m\`. -/
def binomialProduct (p k m : ℕ) : ZMod m :=
  ((p - 1).choose k : ZMod m) * ((p - 1 + k).choose k : ZMod m)

/-- Exact recurrence for the product of the two binomial coefficients. -/
lemma choose_product_step {p k : ℕ} (hk : k + 1 ≤ p - 1) :
    (k + 1) ^ 2 * ((p - 1).choose (k + 1) * (p + k).choose (k + 1)) =
      ((p - 1).choose k * (p - 1 + k).choose k) *
        (p - 1 - k) * (p + k) := by
  have h1 := Nat.choose_succ_right_eq (p - 1) k
  have hs0 : (p - 1 + k).choose k = (p - 1 + k).choose (p - 1) := by
    calc
      (p - 1 + k).choose k =
          (p - 1 + k).choose (p - 1 + k - k) :=
            (Nat.choose_symm (show k ≤ p - 1 + k by omega)).symm
      _ = (p - 1 + k).choose (p - 1) := by
        congr 1
        omega
  have hs1 : (p + k).choose (k + 1) = (p + k).choose (p - 1) := by
    calc
      (p + k).choose (k + 1) =
          (p + k).choose (p + k - (k + 1)) :=
            (Nat.choose_symm (show k + 1 ≤ p + k by omega)).symm
      _ = (p + k).choose (p - 1) := by
        congr 1
        omega
  have h2base := Nat.choose_mul_succ_eq (p - 1 + k) (p - 1)
  have h2 :
      (p + k).choose (k + 1) * (k + 1) =
        (p - 1 + k).choose k * (p + k) := by
    rw [hs0, hs1]
    calc
      (p + k).choose (p - 1) * (k + 1) =
          (p - 1 + k + 1).choose (p - 1) *
            (p - 1 + k + 1 - (p - 1)) := by
              rw [show p + k = p - 1 + k + 1 by omega,
                show p - 1 + k + 1 - (p - 1) = k + 1 by omega]
      _ = (p - 1 + k).choose (p - 1) * (p - 1 + k + 1) := h2base.symm
      _ = (p - 1 + k).choose (p - 1) * (p + k) := by
        congr 1
        omega
  calc
    (k + 1) ^ 2 * ((p - 1).choose (k + 1) * (p + k).choose (k + 1)) =
        ((p - 1).choose (k + 1) * (k + 1)) *
          ((p + k).choose (k + 1) * (k + 1)) := by ring
    _ = ((p - 1).choose k * (p - 1 - k)) *
          ((p - 1 + k).choose k * (p + k)) := by rw [h1, h2]
    _ = _ := by ring

/-- The preceding recurrence after casting into an arbitrary \`ZMod m\`. -/
lemma binomialProduct_step {p k m : ℕ} (hk : k + 1 ≤ p - 1) :
    ((k + 1 : ℕ) : ZMod m) ^ 2 * binomialProduct p (k + 1) m =
      binomialProduct p k m *
        ((p : ZMod m) - 1 - (k : ZMod m)) *
        ((p : ZMod m) + (k : ZMod m)) := by
  have hnat := choose_product_step hk
  have hcast := congrArg (fun n : ℕ => (n : ZMod m)) hnat
  simp only [Nat.cast_mul, Nat.cast_pow] at hcast
  have htop : p - 1 + (k + 1) = p + k := by omega
  have hsubcast :
      ((p - 1 - k : ℕ) : ZMod m) =
        (p : ZMod m) - 1 - (k : ZMod m) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    rfl
  have haddcast :
      ((p + k : ℕ) : ZMod m) = (p : ZMod m) + (k : ZMod m) := by
    push_cast
    rfl
  rw [binomialProduct, binomialProduct, htop]
  rw [← hsubcast, ← haddcast]
  exact hcast

lemma correctionProd_succ (p k m : ℕ) (hk : 1 ≤ k) :
    correctionProd p (k + 1) m =
      correctionProd p k m *
        (1 - (p : ZMod m) ^ 2 * ((k : ZMod m)⁻¹) ^ 2) := by
  rw [correctionProd, correctionProd, Finset.prod_Ico_succ_top hk]

/-- Pure ring identity underlying the induction for \`binomialClosed\`. -/
lemma closed_step_algebra {R : Type*} [CommRing R]
    (s P K U V C : R)
    (hKU : K * U = 1) (hLV : (K + 1) * V = 1) :
    (K + 1) ^ 2 *
        ((-s) * P * V * (1 - P * V) * (C * (1 - P ^ 2 * U ^ 2))) =
      (s * P * U * (1 - P * U) * C) * (P - 1 - K) * (P + K) := by
  have hV :
      (K + 1) ^ 2 * V * (1 - P * V) = K + 1 - P := by
    calc
      (K + 1) ^ 2 * V * (1 - P * V) =
          ((K + 1) * V) * ((K + 1) - P * ((K + 1) * V)) := by ring
      _ = K + 1 - P := by rw [hLV]; ring
  have hU :
      U * (1 - P * U) * (P + K) = 1 - P ^ 2 * U ^ 2 := by
    calc
      U * (1 - P * U) * (P + K) =
          K * U + P * U * (1 - K * U) - P ^ 2 * U ^ 2 := by ring
      _ = 1 - P ^ 2 * U ^ 2 := by rw [hKU]; ring
  calc
    (K + 1) ^ 2 *
        ((-s) * P * V * (1 - P * V) * (C * (1 - P ^ 2 * U ^ 2))) =
      (-s) * P * C * ((K + 1) ^ 2 * V * (1 - P * V)) *
        (1 - P ^ 2 * U ^ 2) := by ring
    _ = (-s) * P * C * (K + 1 - P) * (1 - P ^ 2 * U ^ 2) := by rw [hV]
    _ = s * P * C * (P - 1 - K) * (U * (1 - P * U) * (P + K)) := by
      rw [hU]
      ring
    _ = (s * P * U * (1 - P * U) * C) * (P - 1 - K) * (P + K) := by ring

lemma binomialClosed_step {p k m : ℕ} (hk : 1 ≤ k)
    (hku : IsUnit (k : ZMod m))
    (hksu : IsUnit (((k + 1 : ℕ) : ZMod m))) :
    ((k + 1 : ℕ) : ZMod m) ^ 2 * binomialClosed p (k + 1) m =
      binomialClosed p k m *
        ((p : ZMod m) - 1 - (k : ZMod m)) *
        ((p : ZMod m) + (k : ZMod m)) := by
  have hKU : (k : ZMod m) * (k : ZMod m)⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hku
  have hLV : ((k : ZMod m) + 1) * (((k + 1 : ℕ) : ZMod m))⁻¹ = 1 := by
    convert ZMod.mul_inv_of_unit (((k + 1 : ℕ) : ZMod m)) hksu using 1
    push_cast
    ring
  have hsign : (-1 : ZMod m) ^ (k + 1) = -((-1 : ZMod m) ^ k) := by
    rw [pow_succ]
    ring
  rw [binomialClosed, binomialClosed, correctionProd_succ p k m hk, hsign]
  push_cast
  simpa only [Nat.cast_add, Nat.cast_one] using
    (closed_step_algebra
      ((-1 : ZMod m) ^ k) (p : ZMod m) (k : ZMod m)
      ((k : ZMod m)⁻¹) (((k + 1 : ℕ) : ZMod m)⁻¹)
      (correctionProd p k m) hKU hLV)

lemma binomial_factorization_one {p m : ℕ} (hp : 2 ≤ p) :
    binomialProduct p 1 m = binomialClosed p 1 m := by
  rw [binomialProduct, binomialClosed, correctionProd]
  simp only [Nat.choose_one_right, Finset.Ico_self, Finset.prod_empty, pow_one,
    mul_one]
  have hcast : ((p - 1 : ℕ) : ZMod m) = (p : ZMod m) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  have hp_sub : p - 1 + 1 = p := by omega
  rw [hcast, hp_sub]
  push_cast
  rw [ZMod.inv_one]
  ring

/--
Exact factorization of the binomial product in \`ZMod (p⁴)\`.
Every cancellation is by an explicitly proved unit.
-/
theorem binomialProduct_eq_closed {p k : ℕ} [Fact p.Prime]
    (hk : k ∈ Finset.Icc 1 (p - 1)) :
    binomialProduct p k (p ^ 4) = binomialClosed p k (p ^ 4) := by
  revert hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk
      rcases Finset.mem_Icc.mp hk with ⟨hk1, hkle⟩
      by_cases hk_eq : k = 1
      · subst k
        exact binomial_factorization_one (show p.Prime from Fact.out).two_le
      · have hk2 : 2 ≤ k := by omega
        let j := k - 1
        have hj_lt : j < k := by dsimp [j]; omega
        have hj_plus : j + 1 = k := by dsimp [j]; omega
        have hj_mem : j ∈ Finset.Icc 1 (p - 1) := by
          exact Finset.mem_Icc.mpr ⟨by dsimp [j]; omega, by dsimp [j]; omega⟩
        have hjs_mem : j + 1 ∈ Finset.Icc 1 (p - 1) := by
          rw [hj_plus]
          exact hk
        have ihj := ih j hj_lt hj_mem
        have hju : IsUnit (j : ZMod (p ^ 4)) := by
          rw [ZMod.isUnit_iff_coprime]
          exact (mem_Icc_coprime_prime hj_mem).pow_right 4
        have hjsu : IsUnit (((j + 1 : ℕ) : ZMod (p ^ 4))) := by
          rw [ZMod.isUnit_iff_coprime]
          exact (mem_Icc_coprime_prime hjs_mem).pow_right 4
        have hmul :
            (((j + 1 : ℕ) : ZMod (p ^ 4)) ^ 2) *
                binomialProduct p (j + 1) (p ^ 4) =
              (((j + 1 : ℕ) : ZMod (p ^ 4)) ^ 2) *
                binomialClosed p (j + 1) (p ^ 4) := by
          calc
            _ = binomialProduct p j (p ^ 4) *
                ((p : ZMod (p ^ 4)) - 1 - (j : ZMod (p ^ 4))) *
                ((p : ZMod (p ^ 4)) + (j : ZMod (p ^ 4))) :=
                  binomialProduct_step (by omega)
            _ = binomialClosed p j (p ^ 4) *
                ((p : ZMod (p ^ 4)) - 1 - (j : ZMod (p ^ 4))) *
                ((p : ZMod (p ^ 4)) + (j : ZMod (p ^ 4))) := by rw [ihj]
            _ = _ := (binomialClosed_step (by dsimp [j]; omega) hju hjsu).symm
        have hfactor :
            IsUnit ((((j + 1 : ℕ) : ZMod (p ^ 4)) ^ 2)) := hjsu.pow 2
        have heq :
            binomialProduct p (j + 1) (p ^ 4) =
              binomialClosed p (j + 1) (p ^ 4) :=
          hfactor.mul_left_cancel hmul
        simpa only [hj_plus] using heq

/-! ## First-order truncation of the correction product -/

lemma correctionProd_eq_one_add (p k : ℕ) :
    ∃ T : ZMod (p ^ 4),
      correctionProd p k (p ^ 4) =
        1 + (p : ZMod (p ^ 4)) ^ 2 * T := by
  induction k with
  | zero =>
      refine ⟨0, ?_⟩
      simp [correctionProd]
  | succ k ih =>
      by_cases hk : k = 0
      · subst k
        refine ⟨0, ?_⟩
        simp [correctionProd]
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
        rw [correctionProd_succ p k (p ^ 4) hk1]
        rcases ih with ⟨T, hT⟩
        rw [hT]
        refine
          ⟨T - ((k : ZMod (p ^ 4))⁻¹) ^ 2 -
              (p : ZMod (p ^ 4)) ^ 2 * T *
                ((k : ZMod (p ^ 4))⁻¹) ^ 2, ?_⟩
        ring


/--
A single summand, reduced modulo \`p⁴\`.  This is the formal counterpart of
the first-order product expansion in the paper proof.
-/
lemma mul_p_cube_eq_zero_of_cast_eq_zero {p : ℕ} [Fact p.Prime]
    (x : ZMod (p ^ 4))
    (hx :
      (ZMod.castHom (show p ∣ p ^ 4 by exact dvd_pow_self p (by norm_num))
        (ZMod p)) x = 0) :
    (p : ZMod (p ^ 4)) ^ 3 * x = 0 := by
  let f : ZMod (p ^ 4) →+* ZMod p :=
    ZMod.castHom (show p ∣ p ^ 4 by exact dvd_pow_self p (by norm_num)) (ZMod p)
  have hxval : ((x.val : ℕ) : ZMod p) = 0 := by
    calc
      ((x.val : ℕ) : ZMod p) = f ((x.val : ℕ) : ZMod (p ^ 4)) := by
        simp [f]
      _ = f x := by rw [ZMod.natCast_zmod_val]
      _ = 0 := hx
  have hdvd : p ∣ x.val :=
    (ZMod.natCast_eq_zero_iff x.val p).mp hxval
  rcases hdvd with ⟨q, hq⟩
  rw [← ZMod.natCast_zmod_val x, hq]
  push_cast
  calc
    (p : ZMod (p ^ 4)) ^ 3 * ((p : ZMod (p ^ 4)) * (q : ZMod (p ^ 4))) =
        ((p ^ 4 : ℕ) : ZMod (p ^ 4)) * (q : ZMod (p ^ 4)) := by rw [Nat.cast_pow]; ring
    _ = 0 := by rw [ZMod.natCast_self, zero_mul]


/-- Reduction from \`p⁴\` to \`p\` preserves the inverse of every
representative in \`1, ..., p - 1\`. -/
lemma castHom_inverse_Icc {p k : ℕ} [Fact p.Prime]
    (hk : k ∈ Finset.Icc 1 (p - 1)) :
    (ZMod.castHom (show p ∣ p ^ 4 by exact dvd_pow_self p (by norm_num))
        (ZMod p)) (((k : ZMod (p ^ 4))⁻¹)) =
      ((k : ZMod p)⁻¹) := by
  let f : ZMod (p ^ 4) →+* ZMod p :=
    ZMod.castHom (show p ∣ p ^ 4 by exact dvd_pow_self p (by norm_num)) (ZMod p)
  have hku : IsUnit (k : ZMod (p ^ 4)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (mem_Icc_coprime_prime hk).pow_right 4
  symm
  apply ZMod.inv_eq_of_mul_eq_one
  calc
    (k : ZMod p) * f (((k : ZMod (p ^ 4))⁻¹)) =
        f (k : ZMod (p ^ 4)) * f (((k : ZMod (p ^ 4))⁻¹)) := by
          rw [map_natCast]
    _ = f ((k : ZMod (p ^ 4)) * ((k : ZMod (p ^ 4))⁻¹)) := by
      rw [map_mul]
    _ = f 1 := by rw [ZMod.mul_inv_of_unit _ hku]
    _ = 1 := by rw [map_one]


/-! ## The odd-exponent family -/

/-- The rational sum with exponent 2m+1. -/
def generalizedSum (m : ℤ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 n,
    ((n.choose k : ℚ) ^ 2 * ((n + k).choose k : ℚ) ^ 2) *
      (k : ℚ) ^ (-(2 * m + 1))

/-- The reduced numerator of generalizedSum m n. -/
def u (m : ℤ) (n : ℕ) : ℤ := (generalizedSum m n).num

/-- A representative in 1, ..., p-1, regarded as a unit modulo p^a. -/
def representativeUnit (p a : ℕ) [Fact p.Prime]
    (k : {k : ℕ // k ∈ Finset.Icc 1 (p - 1)}) : (ZMod (p ^ a))ˣ :=
  ZMod.unitOfCoprime k.1 ((mem_Icc_coprime_prime k.2).pow_right a)

/-- The generalized harmonic sum with an arbitrary integer exponent. -/
def harmonicMod (p a : ℕ) [Fact p.Prime] (r : ℤ) : ZMod (p ^ a) :=
  ∑ k : {k : ℕ // k ∈ Finset.Icc 1 (p - 1)},
    ((((representativeUnit p a k)⁻¹) ^ r : (ZMod (p ^ a))ˣ) :
      ZMod (p ^ a))

/-- The binomial sum modulo p^a. -/
def generalizedBinomialSumMod (m : ℤ) (p a : ℕ) [Fact p.Prime] :
    ZMod (p ^ a) :=
  ∑ k : {k : ℕ // k ∈ Finset.Icc 1 (p - 1)},
    (((((representativeUnit p a k)⁻¹) ^ (2 * m + 1) :
        (ZMod (p ^ a))ˣ) : ZMod (p ^ a)) *
      (binomialProduct p k.1 (p ^ a)) ^ 2)

/-- The inverse of a representative unit agrees with the ring inverse. -/
lemma representativeUnit_inv_val {p a : ℕ} [Fact p.Prime]
    (k : {k : ℕ // k ∈ Finset.Icc 1 (p - 1)}) :
    (((representativeUnit p a k)⁻¹ : (ZMod (p ^ a))ˣ) : ZMod (p ^ a)) =
      ((k.1 : ZMod (p ^ a))⁻¹) := by
  symm
  apply ZMod.inv_eq_of_mul_eq_one
  simp [representativeUnit, ZMod.coe_unitOfCoprime]

/-- A first-order binomial formula when the increment has square zero. -/
lemma one_add_pow_of_sq_eq_zero {R : Type*} [CommRing R]
    (x : R) (n : ℕ) (hx : x ^ 2 = 0) :
    (1 + x) ^ n = 1 + (n : R) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, Nat.cast_succ]
      calc
        (1 + (n : R) * x) * (1 + x)
            = 1 + ((n : R) + 1) * x + (n : R) * x ^ 2 := by ring
        _ = 1 + ((n : R) + 1) * x := by rw [hx, mul_zero, add_zero]

/-- The unit 1+x when x²=0. -/
def oneAddSqZeroUnit {R : Type*} [CommRing R]
    (x : R) (hx : x ^ 2 = 0) : Rˣ where
  val := 1 + x
  inv := 1 - x
  val_inv := by
    calc
      (1 + x) * (1 - x) = 1 - x ^ 2 := by ring
      _ = 1 := by rw [hx]; ring
  inv_val := by
    calc
      (1 - x) * (1 + x) = 1 - x ^ 2 := by ring
      _ = 1 := by rw [hx]; ring

/-- First-order expansion of an integer power of 1+x when x²=0. -/
lemma oneAddSqZeroUnit_zpow_val {R : Type*} [CommRing R]
    (x : R) (z : ℤ) (hx : x ^ 2 = 0) :
    (((oneAddSqZeroUnit x hx) ^ z : Rˣ) : R) =
      1 + (z : R) * x := by
  cases z with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
      push_cast
      change (1 + x) ^ n = 1 + (n : R) * x
      exact one_add_pow_of_sq_eq_zero x n hx
  | negSucc n =>
      rw [zpow_negSucc]
      change (1 - x) ^ (n + 1) = _
      have hneg : (-x) ^ 2 = 0 := by rw [neg_sq, hx]
      rw [show 1 - x = 1 + (-x) by ring,
        one_add_pow_of_sq_eq_zero (-x) (n + 1) hneg]
      push_cast
      ring

lemma negOne_zpow_two_mul_add_one {R : Type*} [CommRing R] (m : ℤ) :
    ((-1 : Rˣ) ^ (2 * m + 1)) = -1 := by
  have hone : (-1 : Rˣ) ^ (1 : ℤ) = -1 := zpow_one _
  have hsq : (-1 : Rˣ) ^ (2 : ℤ) = 1 := by
    calc
      (-1 : Rˣ) ^ (2 : ℤ) = (-1 : Rˣ) ^ ((1 : ℤ) + 1) := by norm_num
      _ = (-1 : Rˣ) ^ (1 : ℤ) * (-1 : Rˣ) ^ (1 : ℤ) :=
        zpow_add (-1 : Rˣ) 1 1
      _ = 1 := by rw [zpow_one]; simp
  calc
    (-1 : Rˣ) ^ (2 * m + 1) =
        (-1 : Rˣ) ^ (2 * m) * (-1 : Rˣ) ^ 1 :=
          zpow_add (-1 : Rˣ) (2 * m) 1
    _ = (((-1 : Rˣ) ^ (2 : ℤ)) ^ m) * (-1 : Rˣ) := by
          rw [hone, ← zpow_mul]
    _ = -1 := by rw [hsq, one_zpow, one_mul]

/-- Ring-theoretic core of the summand reduction for integer exponents. -/
lemma generalized_summand_algebra_int {R : Type*} [CommRing R]
    (P : R) (U : Rˣ) (s C : R) (d : ℤ)
    (hs : s ^ 2 = 1) (hPC : P ^ 2 * C ^ 2 = P ^ 2)
    (hP4 : P ^ 4 = 0) :
    (((U ^ d : Rˣ) : R)) *
        (s * P * (U : R) * (1 - P * (U : R)) * C) ^ 2 =
      P ^ 2 * (((U ^ (d + 2) : Rˣ) : R)) -
        2 * P ^ 3 * (((U ^ (d + 3) : Rˣ) : R)) := by
  have hU2 :
      (((U ^ (d + 2) : Rˣ) : R)) =
        (((U ^ d : Rˣ) : R)) * (U : R) ^ 2 := by
    rw [zpow_add]
    norm_num [zpow_ofNat, Units.val_pow_eq_pow_val]
  have hU3 :
      (((U ^ (d + 3) : Rˣ) : R)) =
        (((U ^ d : Rˣ) : R)) * (U : R) ^ 3 := by
    rw [zpow_add]
    norm_num [zpow_ofNat, Units.val_pow_eq_pow_val]
  rw [hU2, hU3]
  calc
    (((U ^ d : Rˣ) : R)) *
        (s * P * (U : R) * (1 - P * (U : R)) * C) ^ 2 =
      (s ^ 2) * (P ^ 2 * C ^ 2) *
        ((((U ^ d : Rˣ) : R)) * (U : R) ^ 2) *
          (1 - P * (U : R)) ^ 2 := by ring
    _ = P ^ 2 * ((((U ^ d : Rˣ) : R)) * (U : R) ^ 2) *
          (1 - P * (U : R)) ^ 2 := by rw [hs, hPC, one_mul]
    _ = P ^ 2 * ((((U ^ d : Rˣ) : R)) * (U : R) ^ 2) -
          2 * P ^ 3 * ((((U ^ d : Rˣ) : R)) * (U : R) ^ 3) +
          P ^ 4 * ((((U ^ d : Rˣ) : R)) * (U : R) ^ 4) := by ring
    _ = P ^ 2 * ((((U ^ d : Rˣ) : R)) * (U : R) ^ 2) -
          2 * P ^ 3 * ((((U ^ d : Rˣ) : R)) * (U : R) ^ 3) := by
            rw [hP4, zero_mul, add_zero]


/-- A single summand reduced modulo p⁴. -/
lemma generalized_binomial_summand_reduction {m : ℤ} {p : ℕ}
    [Fact p.Prime]
    (k : {k : ℕ // k ∈ Finset.Icc 1 (p - 1)}) :
    ((((representativeUnit p 4 k)⁻¹) ^ (2 * m + 1) :
        (ZMod (p ^ 4))ˣ) : ZMod (p ^ 4)) *
        (binomialProduct p k.1 (p ^ 4)) ^ 2 =
      (p : ZMod (p ^ 4)) ^ 2 *
          ((((representativeUnit p 4 k)⁻¹) ^ (2 * m + 3) :
            (ZMod (p ^ 4))ˣ) : ZMod (p ^ 4)) -
        2 * (p : ZMod (p ^ 4)) ^ 3 *
          ((((representativeUnit p 4 k)⁻¹) ^ (2 * m + 4) :
            (ZMod (p ^ 4))ˣ) : ZMod (p ^ 4)) := by
  let P : ZMod (p ^ 4) := p
  let U : (ZMod (p ^ 4))ˣ := (representativeUnit p 4 k)⁻¹
  let C : ZMod (p ^ 4) := correctionProd p k.1 (p ^ 4)
  have hP4 : P ^ 4 = 0 := by
    dsimp [P]
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hsign : ((-1 : ZMod (p ^ 4)) ^ k.1) ^ 2 = 1 := by
    calc
      ((-1 : ZMod (p ^ 4)) ^ k.1) ^ 2 =
          (-1 : ZMod (p ^ 4)) ^ (k.1 * 2) := (pow_mul _ _ _).symm
      _ = (-1 : ZMod (p ^ 4)) ^ (2 * k.1) := by rw [Nat.mul_comm]
      _ = ((-1 : ZMod (p ^ 4)) ^ 2) ^ k.1 := pow_mul _ _ _
      _ = 1 := by norm_num
  rcases correctionProd_eq_one_add p k.1 with ⟨T, hCraw⟩
  have hC : C = 1 + P ^ 2 * T := hCraw
  have hPC : P ^ 2 * C ^ 2 = P ^ 2 := by
    rw [hC]
    calc
      P ^ 2 * (1 + P ^ 2 * T) ^ 2 =
          P ^ 2 + P ^ 4 * (2 * T + P ^ 2 * T ^ 2) := by ring
      _ = P ^ 2 := by rw [hP4]; ring
  have hUval :
      (U : ZMod (p ^ 4)) = ((k.1 : ZMod (p ^ 4))⁻¹) :=
    representativeUnit_inv_val k
  rw [binomialProduct_eq_closed k.2, binomialClosed]
  have hAlg := generalized_summand_algebra_int P U
    ((-1 : ZMod (p ^ 4)) ^ k.1) C (2 * m + 1) hsign hPC hP4
  simpa only [P, U, C, hUval,
    show 2 * m + 1 + 2 = 2 * m + 3 by ring,
    show 2 * m + 1 + 3 = 2 * m + 4 by ring] using hAlg

/-- Summing the pointwise reduction gives two harmonic sums. -/
theorem generalizedBinomialSumMod_reduction {m : ℤ} {p : ℕ}
    [Fact p.Prime] :
    generalizedBinomialSumMod m p 4 =
      (p : ZMod (p ^ 4)) ^ 2 * harmonicMod p 4 (2 * m + 3) -
        2 * (p : ZMod (p ^ 4)) ^ 3 *
          harmonicMod p 4 (2 * m + 4) := by
  rw [generalizedBinomialSumMod, harmonicMod]
  calc
    (∑ k : {k : ℕ // k ∈ Finset.Icc 1 (p - 1)},
      ((((representativeUnit p 4 k)⁻¹) ^ (2 * m + 1) :
          (ZMod (p ^ 4))ˣ) : ZMod (p ^ 4)) *
        (binomialProduct p k.1 (p ^ 4)) ^ 2) =
      ∑ k : {k : ℕ // k ∈ Finset.Icc 1 (p - 1)},
        ((p : ZMod (p ^ 4)) ^ 2 *
            ((((representativeUnit p 4 k)⁻¹) ^ (2 * m + 3) :
              (ZMod (p ^ 4))ˣ) : ZMod (p ^ 4)) -
          2 * (p : ZMod (p ^ 4)) ^ 3 *
            ((((representativeUnit p 4 k)⁻¹) ^ (2 * m + 4) :
              (ZMod (p ^ 4))ˣ) : ZMod (p ^ 4))) := by
          apply Finset.sum_congr rfl
          intro k _
          exact generalized_binomial_summand_reduction k
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, harmonicMod]


/-- First-order expansion of an arbitrary odd integer power. -/
lemma odd_zpow_first_order {R : Type*} [CommRing R]
    (P : R) (U : Rˣ) (m : ℤ) (hP2 : P ^ 2 = 0) :
    (((((-1 : Rˣ) * U *
        oneAddSqZeroUnit (P * (U : R)) (by
          rw [mul_pow, hP2, zero_mul])) ^ (2 * m + 3) : Rˣ) : R)) =
      -(((U ^ (2 * m + 3) : Rˣ) : R)) -
        ((2 * m + 3 : ℤ) : R) * P *
          (((U ^ (2 * m + 4) : Rˣ) : R)) := by
  let A : Rˣ := oneAddSqZeroUnit (P * (U : R)) (by
    rw [mul_pow, hP2, zero_mul])
  have hsign : (-1 : Rˣ) ^ (2 * m + 3) = -1 := by
    convert negOne_zpow_two_mul_add_one (R := R) (m + 1) using 1
    all_goals ring_nf
  have hA :
      (((A ^ (2 * m + 3) : Rˣ) : R)) =
        1 + ((2 * m + 3 : ℤ) : R) * (P * (U : R)) := by
    exact oneAddSqZeroUnit_zpow_val _ _ _
  have hz := congrArg (fun x : Rˣ => (x : R))
    (zpow_add U (2 * m + 3) 1)
  change
    (((U ^ (2 * m + 3 + 1) : Rˣ) : R)) =
      (((U ^ (2 * m + 3) : Rˣ) : R)) *
        (((U ^ (1 : ℤ) : Rˣ) : R)) at hz
  rw [zpow_one] at hz
  have hUnext :
      (((U ^ (2 * m + 4) : Rˣ) : R)) =
        (((U ^ (2 * m + 3) : Rˣ) : R)) * (U : R) := by
    convert hz using 1
    all_goals ring_nf
  change (((((-1 : Rˣ) * U * A) ^ (2 * m + 3) : Rˣ) : R)) = _
  rw [mul_zpow, mul_zpow, hsign]
  change
    (-1 : R) * (((U ^ (2 * m + 3) : Rˣ) : R)) *
      (((A ^ (2 * m + 3) : Rˣ) : R)) = _
  rw [hA, hUnext]
  ring

/-- The pointwise reflection formula in ZMod (p²). -/
lemma paired_inverse_odd {m : ℤ} {p : ℕ} [Fact p.Prime]
    (k : {k : ℕ // k ∈ Finset.Icc 1 (p - 1)}) :
    ((((representativeUnit p 2 (reflectionEquiv p k))⁻¹) ^
        (2 * m + 3) : (ZMod (p ^ 2))ˣ) : ZMod (p ^ 2)) =
      -((((representativeUnit p 2 k)⁻¹) ^ (2 * m + 3) :
        (ZMod (p ^ 2))ˣ) : ZMod (p ^ 2)) -
        ((2 * m + 3 : ℤ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
          ((((representativeUnit p 2 k)⁻¹) ^ (2 * m + 4) :
            (ZMod (p ^ 2))ˣ) : ZMod (p ^ 2)) := by
  let P : ZMod (p ^ 2) := p
  let K : (ZMod (p ^ 2))ˣ := representativeUnit p 2 k
  let U : (ZMod (p ^ 2))ˣ := K⁻¹
  let V : (ZMod (p ^ 2))ˣ :=
    (representativeUnit p 2 (reflectionEquiv p k))⁻¹
  have hk_bounds := Finset.mem_Icc.mp k.2
  have hk_le : k.1 ≤ p := by omega
  have hP2 : P ^ 2 = 0 := by
    dsimp [P]
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hUval : (U : ZMod (p ^ 2)) = ((k.1 : ZMod (p ^ 2))⁻¹) :=
    representativeUnit_inv_val k
  have hVval :
      (V : ZMod (p ^ 2)) =
        (((p - k.1 : ℕ) : ZMod (p ^ 2))⁻¹) := by
    exact representativeUnit_inv_val (reflectionEquiv p k)
  have hcast : ((p - k.1 : ℕ) : ZMod (p ^ 2)) =
      P - (k.1 : ZMod (p ^ 2)) := by
    dsimp [P]
    rw [Nat.cast_sub hk_le]
  have hKU :
      (k.1 : ZMod (p ^ 2)) * (U : ZMod (p ^ 2)) = 1 := by
    rw [hUval]
    apply ZMod.mul_inv_of_unit
    change IsUnit (k.1 : ZMod (p ^ 2))
    rw [ZMod.isUnit_iff_coprime]
    exact (mem_Icc_coprime_prime k.2).pow_right 2
  have hinv :
      (((p - k.1 : ℕ) : ZMod (p ^ 2))⁻¹) =
        -(U : ZMod (p ^ 2)) - P * (U : ZMod (p ^ 2)) ^ 2 := by
    apply ZMod.inv_eq_of_mul_eq_one
    rw [hcast]
    calc
      (P - (k.1 : ZMod (p ^ 2))) *
          (-(U : ZMod (p ^ 2)) - P * (U : ZMod (p ^ 2)) ^ 2) =
        (k.1 : ZMod (p ^ 2)) * (U : ZMod (p ^ 2)) +
          P * (U : ZMod (p ^ 2)) *
            ((k.1 : ZMod (p ^ 2)) * (U : ZMod (p ^ 2)) - 1) -
          P ^ 2 * (U : ZMod (p ^ 2)) ^ 2 := by ring
      _ = 1 := by rw [hKU, hP2]; ring
  let A : (ZMod (p ^ 2))ˣ :=
    oneAddSqZeroUnit (P * (U : ZMod (p ^ 2))) (by
      rw [mul_pow, hP2, zero_mul])
  have hVunit : V = (-1 : (ZMod (p ^ 2))ˣ) * U * A := by
    apply Units.ext
    rw [hVval, hinv]
    change
      -(U : ZMod (p ^ 2)) - P * (U : ZMod (p ^ 2)) ^ 2 =
        (-1 : ZMod (p ^ 2)) * (U : ZMod (p ^ 2)) *
          (1 + P * (U : ZMod (p ^ 2)))
    ring
  change (((V ^ (2 * m + 3) : (ZMod (p ^ 2))ˣ) : ZMod (p ^ 2))) = _
  rw [hVunit]
  exact odd_zpow_first_order P U m hP2

/-- Pairing k with p-k for every exponent 2m+3. -/
lemma harmonic_pairing_odd {m : ℤ} {p : ℕ} [Fact p.Prime] :
    2 * harmonicMod p 2 (2 * m + 3) =
      -((2 * m + 3 : ℤ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
        harmonicMod p 2 (2 * m + 4) := by
  have hperm :
      (∑ k : {k : ℕ // k ∈ Finset.Icc 1 (p - 1)},
        ((((representativeUnit p 2 (reflectionEquiv p k))⁻¹) ^
          (2 * m + 3) : (ZMod (p ^ 2))ˣ) : ZMod (p ^ 2))) =
        harmonicMod p 2 (2 * m + 3) := by
    rw [harmonicMod]
    apply Fintype.sum_equiv (reflectionEquiv p)
    intro k
    rfl
  have hrel :
      harmonicMod p 2 (2 * m + 3) =
        -harmonicMod p 2 (2 * m + 3) -
          ((2 * m + 3 : ℤ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
            harmonicMod p 2 (2 * m + 4) := by
    calc
      harmonicMod p 2 (2 * m + 3) =
          ∑ k : {k : ℕ // k ∈ Finset.Icc 1 (p - 1)},
            ((((representativeUnit p 2 (reflectionEquiv p k))⁻¹) ^
              (2 * m + 3) : (ZMod (p ^ 2))ˣ) : ZMod (p ^ 2)) :=
                hperm.symm
      _ = ∑ k : {k : ℕ // k ∈ Finset.Icc 1 (p - 1)},
          (-((((representativeUnit p 2 k)⁻¹) ^ (2 * m + 3) :
              (ZMod (p ^ 2))ˣ) : ZMod (p ^ 2)) -
            ((2 * m + 3 : ℤ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
              ((((representativeUnit p 2 k)⁻¹) ^ (2 * m + 4) :
                (ZMod (p ^ 2))ˣ) : ZMod (p ^ 2))) := by
          apply Finset.sum_congr rfl
          intro k _
          exact paired_inverse_odd k
      _ = -harmonicMod p 2 (2 * m + 3) -
          ((2 * m + 3 : ℤ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
            harmonicMod p 2 (2 * m + 4) := by
          simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
          rw [← Finset.mul_sum]
          rfl
  calc
    2 * harmonicMod p 2 (2 * m + 3) =
        harmonicMod p 2 (2 * m + 3) +
          harmonicMod p 2 (2 * m + 3) := by ring
    _ = harmonicMod p 2 (2 * m + 3) +
        (-harmonicMod p 2 (2 * m + 3) -
          ((2 * m + 3 : ℤ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
            harmonicMod p 2 (2 * m + 4)) :=
      congrArg (fun x => harmonicMod p 2 (2 * m + 3) + x) hrel
    _ = _ := by ring



/-- Vanishing modulo p² can be lifted after multiplication by p². -/
lemma mul_p_sq_eq_zero_of_cast_eq_zero {p : ℕ} [Fact p.Prime]
    (x : ZMod (p ^ 4))
    (hx :
      (ZMod.castHom
        (show p ^ 2 ∣ p ^ 4 by
          use p ^ 2
          ring)
        (ZMod (p ^ 2))) x = 0) :
    (p : ZMod (p ^ 4)) ^ 2 * x = 0 := by
  let f : ZMod (p ^ 4) →+* ZMod (p ^ 2) :=
    ZMod.castHom
      (show p ^ 2 ∣ p ^ 4 by
        use p ^ 2
        ring)
      (ZMod (p ^ 2))
  have hxval : ((x.val : ℕ) : ZMod (p ^ 2)) = 0 := by
    calc
      ((x.val : ℕ) : ZMod (p ^ 2)) =
          f ((x.val : ℕ) : ZMod (p ^ 4)) := by simp [f]
      _ = f x := by rw [ZMod.natCast_zmod_val]
      _ = 0 := hx
  have hdvd : p ^ 2 ∣ x.val :=
    (ZMod.natCast_eq_zero_iff x.val (p ^ 2)).mp hxval
  rcases hdvd with ⟨q, hq⟩
  rw [← ZMod.natCast_zmod_val x, hq]
  push_cast
  calc
    (p : ZMod (p ^ 4)) ^ 2 *
        (((p : ZMod (p ^ 4)) ^ 2) * (q : ZMod (p ^ 4))) =
      ((p ^ 4 : ℕ) : ZMod (p ^ 4)) * (q : ZMod (p ^ 4)) := by
        rw [Nat.cast_pow]
        ring
    _ = 0 := by rw [ZMod.natCast_self, zero_mul]

/-- Reduction maps integer powers of representative units compatibly. -/
lemma castHom_representativeUnit_inv_zpow {p a b : ℕ} [Fact p.Prime]
    (hba : p ^ b ∣ p ^ a)
    (k : {k : ℕ // k ∈ Finset.Icc 1 (p - 1)}) (z : ℤ) :
    (ZMod.castHom hba (ZMod (p ^ b)))
        ((((representativeUnit p a k)⁻¹) ^ z : (ZMod (p ^ a))ˣ) :
          ZMod (p ^ a)) =
      ((((representativeUnit p b k)⁻¹) ^ z : (ZMod (p ^ b))ˣ) :
        ZMod (p ^ b)) := by
  let f : ZMod (p ^ a) →+* ZMod (p ^ b) :=
    ZMod.castHom hba (ZMod (p ^ b))
  let F : (ZMod (p ^ a))ˣ →* (ZMod (p ^ b))ˣ :=
    Units.map f.toMonoidHom
  have hunit : F (representativeUnit p a k) = representativeUnit p b k := by
    apply Units.ext
    change f (k.1 : ZMod (p ^ a)) = (k.1 : ZMod (p ^ b))
    simp [f]
  change f
      ((((representativeUnit p a k)⁻¹) ^ z : (ZMod (p ^ a))ˣ) :
        ZMod (p ^ a)) = _
  calc
    f ((((representativeUnit p a k)⁻¹) ^ z :
          (ZMod (p ^ a))ˣ) : ZMod (p ^ a)) =
      ((F (((representativeUnit p a k)⁻¹) ^ z) :
        (ZMod (p ^ b))ˣ) : ZMod (p ^ b)) := rfl
    _ = (((F ((representativeUnit p a k)⁻¹)) ^ z :
        (ZMod (p ^ b))ˣ) : ZMod (p ^ b)) := by rw [map_zpow]
    _ = _ := by rw [map_inv, hunit]

/-- Harmonic sums commute with reduction from p⁴ to p². -/
lemma castHom_harmonic_sq {p : ℕ} [Fact p.Prime] (r : ℤ) :
    (ZMod.castHom
      (show p ^ 2 ∣ p ^ 4 by
        use p ^ 2
        ring)
      (ZMod (p ^ 2))) (harmonicMod p 4 r) =
        harmonicMod p 2 r := by
  rw [harmonicMod, harmonicMod, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact castHom_representativeUnit_inv_zpow _ k r

/-- The harmonic pairing at modulus p⁴, with its factor p². -/
theorem generalized_harmonic_pairing_mul_p_sq {m : ℤ} {p : ℕ}
    [Fact p.Prime] :
    (p : ZMod (p ^ 4)) ^ 2 *
      (2 * harmonicMod p 4 (2 * m + 3) +
        ((2 * m + 3 : ℤ) : ZMod (p ^ 4)) * (p : ZMod (p ^ 4)) *
          harmonicMod p 4 (2 * m + 4)) = 0 := by
  apply mul_p_sq_eq_zero_of_cast_eq_zero
  simp only [map_add, map_mul, map_intCast, map_natCast, map_ofNat,
    castHom_harmonic_sq]
  rw [harmonic_pairing_odd]
  ring

/-- The coefficient form of the key reduction. -/
lemma key_reduction_scaled_general {R : Type*} [CommRing R]
    (P Hr He S c : R)
    (hS : S = P ^ 2 * Hr - 2 * P ^ 3 * He)
    (hH : P ^ 2 * (2 * Hr + c * P * He) = 0) :
    2 * S = -(c + 4) * P ^ 3 * He := by
  rw [hS]
  calc
    2 * (P ^ 2 * Hr - 2 * P ^ 3 * He) =
        P ^ 2 * (2 * Hr + c * P * He) -
          (c + 4) * P ^ 3 * He := by ring
    _ = -(c + 4) * P ^ 3 * He := by rw [hH]; ring

/-- The central congruence for an arbitrary integer parameter. -/
theorem generalized_key_congruence {m : ℤ} {p : ℕ} [Fact p.Prime] :
    2 * generalizedBinomialSumMod m p 4 =
      -((2 * m + 7 : ℤ) : ZMod (p ^ 4)) *
        (p : ZMod (p ^ 4)) ^ 3 *
          harmonicMod p 4 (2 * m + 4) := by
  let P : ZMod (p ^ 4) := p
  let Hr := harmonicMod p 4 (2 * m + 3)
  let He := harmonicMod p 4 (2 * m + 4)
  let S := generalizedBinomialSumMod m p 4
  have hS : S = P ^ 2 * Hr - 2 * P ^ 3 * He :=
    generalizedBinomialSumMod_reduction
  have hH :
      P ^ 2 *
        (2 * Hr + ((2 * m + 3 : ℤ) : ZMod (p ^ 4)) * P * He) = 0 :=
    generalized_harmonic_pairing_mul_p_sq
  have hkey := key_reduction_scaled_general P Hr He S
    (((2 * m + 3 : ℤ) : ZMod (p ^ 4))) hS hH
  dsimp [S, P, He] at hkey ⊢
  convert hkey using 1
  all_goals
    push_cast
    ring_nf



/-! ### The finite-field obstruction -/

/-- Integer powers over the unit group reduce to a natural power sum. -/
lemma sum_units_zpow_eq_sum_pow_natAbs {p : ℕ} [Fact p.Prime] (e : ℤ) :
    (∑ x : (ZMod p)ˣ, (((x ^ e : (ZMod p)ˣ) : ZMod p))) =
      ∑ x : (ZMod p)ˣ, (x : ZMod p) ^ e.natAbs := by
  cases e with
  | ofNat n =>
      simp only [Int.ofNat_eq_natCast, zpow_natCast,
        Units.val_pow_eq_pow_val, Int.natAbs_natCast]
  | negSucc n =>
      apply Fintype.sum_equiv (Equiv.inv ((ZMod p)ˣ))
      intro x
      simp only [Equiv.inv_apply, Int.natAbs_negSucc, zpow_negSucc]
      change
        (((x ^ (n + 1))⁻¹ : (ZMod p)ˣ) : ZMod p) =
          (((x⁻¹ : (ZMod p)ˣ) : ZMod p)) ^ (n + 1)
      rw [← Units.val_pow_eq_pow_val]
      congr 1

/-- A unit-group integer power sum vanishes unless the group order divides
the exponent. -/
theorem sum_units_zpow_eq_zero_of_not_dvd {p : ℕ} [Fact p.Prime]
    {e : ℤ} (hnot : ¬ ((p - 1 : ℕ) : ℤ) ∣ e) :
    (∑ x : (ZMod p)ˣ, (((x ^ e : (ZMod p)ˣ) : ZMod p))) = 0 := by
  rw [sum_units_zpow_eq_sum_pow_natAbs]
  rw [FiniteField.sum_pow_units]
  have hnat : ¬ p - 1 ∣ e.natAbs := by
    simpa only [Int.natCast_dvd] using hnot
  simp only [ZMod.card, hnat, ↓reduceIte]

/-- Inversion permutes the units for every integer exponent. -/
lemma sum_inverse_zpowers_units (p : ℕ) [Fact p.Prime] (e : ℤ) :
    (∑ x : (ZMod p)ˣ,
      (((((x⁻¹ : (ZMod p)ˣ) ^ e : (ZMod p)ˣ)) : ZMod p))) =
      ∑ x : (ZMod p)ˣ, (((x ^ e : (ZMod p)ˣ) : ZMod p)) := by
  apply Fintype.sum_equiv (Equiv.inv ((ZMod p)ˣ))
  intro x
  rfl

/-- The harmonic sum in the prime field. -/
def harmonicModPrime (p : ℕ) [Fact p.Prime] (e : ℤ) : ZMod p :=
  ∑ k : {k : ℕ // k ∈ Finset.Icc 1 (p - 1)},
    (((((ZMod.unitOfCoprime k.1 (mem_Icc_coprime_prime k.2))⁻¹) ^ e :
      (ZMod p)ˣ) : ZMod p))

/-- The harmonic sum vanishes in the prime field under the
finite-field condition. -/
theorem harmonicPrime_eq_zero {p : ℕ} [Fact p.Prime] {e : ℤ}
    (hnot : ¬ ((p - 1 : ℕ) : ℤ) ∣ e) :
    harmonicModPrime p e = 0 := by
  rw [harmonicModPrime]
  calc
    (∑ k : {k : ℕ // k ∈ Finset.Icc 1 (p - 1)},
      (((((ZMod.unitOfCoprime k.1 (mem_Icc_coprime_prime k.2))⁻¹) ^ e :
        (ZMod p)ˣ) : ZMod p))) =
      ∑ x : (ZMod p)ˣ,
        (((((x⁻¹ : (ZMod p)ˣ) ^ e : (ZMod p)ˣ)) : ZMod p)) := by
          apply Fintype.sum_equiv (residueUnitEquiv p)
          intro k
          rfl
    _ = ∑ x : (ZMod p)ˣ, (((x ^ e : (ZMod p)ˣ) : ZMod p)) :=
      sum_inverse_zpowers_units p e
    _ = 0 := sum_units_zpow_eq_zero_of_not_dvd hnot


/-- Reduction from p⁴ to p commutes with every harmonic sum. -/
lemma castHom_harmonic_prime {p : ℕ} [Fact p.Prime] (e : ℤ) :
    (ZMod.castHom (show p ∣ p ^ 4 by exact dvd_pow_self p (by norm_num))
      (ZMod p)) (harmonicMod p 4 e) =
        harmonicModPrime p e := by
  let f : ZMod (p ^ 4) →+* ZMod p :=
    ZMod.castHom (show p ∣ p ^ 4 by exact dvd_pow_self p (by norm_num))
      (ZMod p)
  let F : (ZMod (p ^ 4))ˣ →* (ZMod p)ˣ := Units.map f.toMonoidHom
  rw [harmonicMod, harmonicModPrime, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  let K4 : (ZMod (p ^ 4))ˣ := representativeUnit p 4 k
  let Kp : (ZMod p)ˣ :=
    ZMod.unitOfCoprime k.1 (mem_Icc_coprime_prime k.2)
  have hunit : F K4 = Kp := by
    apply Units.ext
    change f (k.1 : ZMod (p ^ 4)) = (k.1 : ZMod p)
    simp [f]
  change f (((K4⁻¹) ^ e : (ZMod (p ^ 4))ˣ) : ZMod (p ^ 4)) =
    ((((Kp⁻¹) ^ e : (ZMod p)ˣ) : ZMod p))
  calc
    f ((((K4⁻¹) ^ e : (ZMod (p ^ 4))ˣ) : ZMod (p ^ 4))) =
      ((F ((K4⁻¹) ^ e) : (ZMod p)ˣ) : ZMod p) := rfl
    _ = (((F K4⁻¹) ^ e : (ZMod p)ˣ) : ZMod p) := by rw [map_zpow]
    _ = _ := by rw [map_inv, hunit]

/-- Finite-field vanishing lifted to ZMod (p⁴). -/
theorem harmonic_mul_p_cube_eq_zero_of_not_dvd {p : ℕ} [Fact p.Prime]
    {e : ℤ} (hnot : ¬ ((p - 1 : ℕ) : ℤ) ∣ e) :
    (p : ZMod (p ^ 4)) ^ 3 * harmonicMod p 4 e = 0 := by
  apply mul_p_cube_eq_zero_of_cast_eq_zero
  rw [castHom_harmonic_prime]
  exact harmonicPrime_eq_zero hnot

/-- If p divides an integer coefficient, its product with p³ vanishes
modulo p⁴. -/
lemma coefficient_mul_p_cube_eq_zero_of_dvd {p : ℕ} {c : ℤ}
    (hpc : (p : ℤ) ∣ c) (x : ZMod (p ^ 4)) :
    (c : ZMod (p ^ 4)) * (p : ZMod (p ^ 4)) ^ 3 * x = 0 := by
  rcases hpc with ⟨q, hq⟩
  rw [hq]
  push_cast
  calc
    ((p : ZMod (p ^ 4)) * (q : ZMod (p ^ 4))) *
        (p : ZMod (p ^ 4)) ^ 3 * x =
      ((p ^ 4 : ℕ) : ZMod (p ^ 4)) * (q : ZMod (p ^ 4)) * x := by
        rw [Nat.cast_pow]
        ring
    _ = 0 := by rw [ZMod.natCast_self]; ring

/-- Two is a unit modulo p⁴ for every odd prime p. -/
lemma two_isUnit_mod_prime_four {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    IsUnit (2 : ZMod (p ^ 4)) := by
  have hnot : ¬ 2 ∣ p := by
    intro hdiv
    rcases (Nat.dvd_prime (show p.Prime from Fact.out)).mp hdiv with h | h
    · norm_num at h
    · omega
  change IsUnit ((2 : ℕ) : ZMod (p ^ 4))
  rw [ZMod.isUnit_iff_coprime]
  exact ((Nat.prime_two.coprime_iff_not_dvd).mpr hnot).pow_right 4

/-- The modular sum vanishes under the stated arithmetic condition. -/
theorem generalizedBinomialSumMod_eq_zero {m : ℤ} {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2)
    (hgood :
      (¬ ((p - 1 : ℕ) : ℤ) ∣ 2 * m + 4) ∨
        (p : ℤ) ∣ 2 * m + 7) :
    generalizedBinomialSumMod m p 4 = 0 := by
  let P : ZMod (p ^ 4) := p
  let H := harmonicMod p 4 (2 * m + 4)
  let S := generalizedBinomialSumMod m p 4
  have hright :
      ((2 * m + 7 : ℤ) : ZMod (p ^ 4)) * P ^ 3 * H = 0 := by
    rcases hgood with hnot | hdiv
    · have hH : P ^ 3 * H = 0 :=
        harmonic_mul_p_cube_eq_zero_of_not_dvd hnot
      calc
        ((2 * m + 7 : ℤ) : ZMod (p ^ 4)) * P ^ 3 * H =
            ((2 * m + 7 : ℤ) : ZMod (p ^ 4)) * (P ^ 3 * H) := by ring
        _ = 0 := by rw [hH, mul_zero]
    · exact coefficient_mul_p_cube_eq_zero_of_dvd hdiv H
  have h2 : IsUnit (2 : ZMod (p ^ 4)) :=
    two_isUnit_mod_prime_four hp2
  apply h2.mul_left_cancel
  calc
    2 * S =
        -((2 * m + 7 : ℤ) : ZMod (p ^ 4)) * P ^ 3 * H :=
      generalized_key_congruence
    _ = -(((2 * m + 7 : ℤ) : ZMod (p ^ 4)) * P ^ 3 * H) := by ring
    _ = 0 := by rw [hright, neg_zero]
    _ = 2 * 0 := by ring

/-- The exceptional primes for the parameter m. -/
def exceptionalPrimes (m : ℤ) : Set ℕ :=
  {p | p.Prime ∧
    ((p - 1 : ℕ) : ℤ) ∣ 2 * m + 4 ∧
    ¬ (p : ℤ) ∣ 2 * m + 7}

theorem mem_exceptionalPrimes_iff {m : ℤ} {p : ℕ} :
    p ∈ exceptionalPrimes m ↔
      p.Prime ∧
        ((p - 1 : ℕ) : ℤ) ∣ 2 * m + 4 ∧
        ¬ (p : ℤ) ∣ 2 * m + 7 := by
  rfl

/-- Every prime outside the exceptional set has vanishing modular sum. -/
theorem generalizedBinomialSumMod_eq_zero_of_not_mem
    {m : ℤ} {p : ℕ} [Fact p.Prime]
    (hpnot : p ∉ exceptionalPrimes m) :
    generalizedBinomialSumMod m p 4 = 0 := by
  have hp2 : p ≠ 2 := by
    intro hp
    subst p
    apply hpnot
    rw [mem_exceptionalPrimes_iff]
    refine ⟨Nat.prime_two, by norm_num, ?_⟩
    intro hdiv
    rcases hdiv with ⟨q, hq⟩
    omega
  have hgood :
      (¬ ((p - 1 : ℕ) : ℤ) ∣ 2 * m + 4) ∨
        (p : ℤ) ∣ 2 * m + 7 := by
    by_cases hdiv : ((p - 1 : ℕ) : ℤ) ∣ 2 * m + 4
    · right
      by_contra hcoeff
      apply hpnot
      rw [mem_exceptionalPrimes_iff]
      exact ⟨Fact.out, hdiv, hcoeff⟩
    · exact Or.inl hdiv
  exact generalizedBinomialSumMod_eq_zero hp2 hgood


/-! ### Passage to the reduced rational numerator -/

/-- Splitting an integer exponent into numerator and denominator parts. -/
lemma rat_zpow_neg_eq_split (x : ℚ) (d : ℤ) :
    x ^ (-d) = x ^ (-d).toNat / x ^ d.toNat := by
  cases d with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_neg, zpow_natCast]
      simp
  | negSucc n =>
      rw [Int.negSucc_eq]
      simp only [neg_neg]
      have hpos : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
      rw [hpos, zpow_natCast]
      have hzero : (-((n + 1 : ℕ) : ℤ)).toNat = 0 :=
        Int.toNat_of_nonpos (by omega)
      rw [Int.toNat_natCast, hzero, pow_zero, div_one]

/-- The denominator exponent contributed by 2m+1. -/
def denominatorExponent (m : ℤ) : ℕ := (2 * m + 1).toNat

/-- The numerator exponent contributed by 2m+1. -/
def numeratorExponent (m : ℤ) : ℕ := (-(2 * m + 1)).toNat

/-- A common denominator for the rational sum. -/
def generalizedCommonDen (m : ℤ) (p : ℕ) : ℕ :=
  (Nat.factorial (p - 1)) ^ denominatorExponent m

/-- The numerator before cancellation of the common denominator. -/
def generalizedCommonNumerator (m : ℤ) (p : ℕ) : ℕ :=
  ∑ k : {k : ℕ // k ∈ Finset.Icc 1 (p - 1)},
    (((p - 1).choose k.1 * (p - 1 + k.1).choose k.1) ^ 2) *
      k.1 ^ numeratorExponent m *
      (generalizedCommonDen m p / k.1 ^ denominatorExponent m)

/-- Each denominator power divides the common denominator. -/
lemma denominator_power_dvd_generalizedCommonDen {m : ℤ} {p k : ℕ}
    (hk : k ∈ Finset.Icc 1 (p - 1)) :
    k ^ denominatorExponent m ∣ generalizedCommonDen m p := by
  rw [generalizedCommonDen]
  exact pow_dvd_pow_of_dvd
    (Nat.dvd_factorial (Finset.mem_Icc.mp hk).1
      (Finset.mem_Icc.mp hk).2) (denominatorExponent m)

/-- One rational summand over the explicit common denominator. -/
lemma generalized_rational_summand_eq_commonDen {m : ℤ} {p k : ℕ}
    (hk : k ∈ Finset.Icc 1 (p - 1)) :
    ((p - 1).choose k : ℚ) ^ 2 *
        ((p - 1 + k).choose k : ℚ) ^ 2 *
          (k : ℚ) ^ (-(2 * m + 1)) =
      ((((p - 1).choose k * (p - 1 + k).choose k) ^ 2 *
          k ^ numeratorExponent m *
          (generalizedCommonDen m p / k ^ denominatorExponent m) : ℕ) : ℚ) /
        (generalizedCommonDen m p : ℚ) := by
  have hk0 : k ≠ 0 := by
    have := (Finset.mem_Icc.mp hk).1
    omega
  have hD0 : generalizedCommonDen m p ≠ 0 := by
    rw [generalizedCommonDen]
    exact pow_ne_zero _ (Nat.factorial_ne_zero _)
  have hmul :=
    Nat.mul_div_cancel'
      (denominator_power_dvd_generalizedCommonDen (m := m) hk)
  have hDq :
      (generalizedCommonDen m p : ℚ) =
        (k : ℚ) ^ denominatorExponent m *
          (generalizedCommonDen m p / k ^ denominatorExponent m : ℕ) := by
    exact_mod_cast hmul.symm
  rw [rat_zpow_neg_eq_split]
  change
    ((p - 1).choose k : ℚ) ^ 2 *
        ((p - 1 + k).choose k : ℚ) ^ 2 *
          ((k : ℚ) ^ numeratorExponent m /
            (k : ℚ) ^ denominatorExponent m) = _
  field_simp [hk0, hD0]
  rw [hDq]
  push_cast
  ring

/-- The rational sum over its explicit common denominator. -/
theorem generalizedSum_eq_commonNumerator_div (m : ℤ) (p : ℕ) :
    generalizedSum m (p - 1) =
      (generalizedCommonNumerator m p : ℚ) /
        (generalizedCommonDen m p : ℚ) := by
  rw [generalizedSum, generalizedCommonNumerator]
  rw [Finset.sum_subtype (Finset.Icc 1 (p - 1)) (fun _ => Iff.rfl)]
  calc
    (∑ k : {k : ℕ // k ∈ Finset.Icc 1 (p - 1)},
      (((p - 1).choose k.1 : ℚ) ^ 2 *
        ((p - 1 + k.1).choose k.1 : ℚ) ^ 2 *
          (k.1 : ℚ) ^ (-(2 * m + 1)))) =
      ∑ k : {k : ℕ // k ∈ Finset.Icc 1 (p - 1)},
        (((((p - 1).choose k.1 * (p - 1 + k.1).choose k.1) ^ 2 *
          k.1 ^ numeratorExponent m *
          (generalizedCommonDen m p /
            k.1 ^ denominatorExponent m) : ℕ) : ℚ) /
              (generalizedCommonDen m p : ℚ)) := by
          apply Finset.sum_congr rfl
          intro k _
          exact generalized_rational_summand_eq_commonDen k.2
    _ = _ := by
      simp only [div_eq_mul_inv]
      push_cast
      rw [Finset.sum_mul]



/-- Cancelling the denominator part of an integer power leaves its numerator part. -/
lemma unit_pow_toNat_mul_inv_zpow {G : Type*} [Group G]
    (K : G) (d : ℤ) :
    K ^ d.toNat * (K⁻¹) ^ d = K ^ (-d).toNat := by
  cases d with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast]
      simp
  | negSucc n =>
      have hzero : (Int.negSucc n).toNat = 0 :=
        Int.toNat_of_nonpos (by omega)
      rw [hzero, pow_zero, one_mul]
      rw [Int.negSucc_eq]
      simp only [neg_neg]
      have hpos : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
      rw [hpos, zpow_neg, zpow_natCast, Int.toNat_natCast]
      simp

/-- Multiplication by the common denominator clears one modular summand. -/
lemma generalizedCommonDen_mul_binomial_summand
    {m : ℤ} {p : ℕ} [Fact p.Prime]
    (k : {k : ℕ // k ∈ Finset.Icc 1 (p - 1)}) :
    (generalizedCommonDen m p : ZMod (p ^ 4)) *
        (((((representativeUnit p 4 k)⁻¹) ^ (2 * m + 1) :
            (ZMod (p ^ 4))ˣ) : ZMod (p ^ 4)) *
          (binomialProduct p k.1 (p ^ 4)) ^ 2) =
      ((((p - 1).choose k.1 * (p - 1 + k.1).choose k.1) ^ 2 *
          k.1 ^ numeratorExponent m *
          (generalizedCommonDen m p /
            k.1 ^ denominatorExponent m) : ℕ) : ZMod (p ^ 4)) := by
  let K := representativeUnit p 4 k
  let U := K⁻¹
  let V : ZMod (p ^ 4) :=
    ((U ^ (2 * m + 1) : (ZMod (p ^ 4))ˣ) : ZMod (p ^ 4))
  let B : ZMod (p ^ 4) :=
    ((p - 1).choose k.1 * (p - 1 + k.1).choose k.1 : ℕ)
  let Q : ZMod (p ^ 4) :=
    (generalizedCommonDen m p /
      k.1 ^ denominatorExponent m : ℕ)
  have hmul :=
    Nat.mul_div_cancel'
      (denominator_power_dvd_generalizedCommonDen (m := m) k.2)
  have hDcast :
      (generalizedCommonDen m p : ZMod (p ^ 4)) =
        (K : ZMod (p ^ 4)) ^ denominatorExponent m * Q := by
    have hcast := congrArg
      (fun n : ℕ => (n : ZMod (p ^ 4))) hmul.symm
    simp only [Nat.cast_mul, Nat.cast_pow] at hcast
    simpa [K, Q, representativeUnit, ZMod.coe_unitOfCoprime] using hcast
  have hBcast :
      ((p - 1).choose k.1 : ZMod (p ^ 4)) *
          ((p - 1 + k.1).choose k.1 : ZMod (p ^ 4)) = B := by
    dsimp [B]
    push_cast
    rfl
  have hcancel :
      (K : ZMod (p ^ 4)) ^ denominatorExponent m * V =
        (K : ZMod (p ^ 4)) ^ numeratorExponent m := by
    have h := unit_pow_toNat_mul_inv_zpow K (2 * m + 1)
    have hval := congrArg
      (fun W : (ZMod (p ^ 4))ˣ => (W : ZMod (p ^ 4))) h
    simpa [U, V, denominatorExponent, numeratorExponent] using hval
  rw [binomialProduct, hBcast]
  change
    (generalizedCommonDen m p : ZMod (p ^ 4)) *
      (V * B ^ 2) = _
  push_cast
  rw [hBcast]
  change
    (generalizedCommonDen m p : ZMod (p ^ 4)) *
      (V * B ^ 2) =
        B ^ 2 * (K : ZMod (p ^ 4)) ^ numeratorExponent m * Q
  rw [hDcast]
  calc
    ((K : ZMod (p ^ 4)) ^ denominatorExponent m * Q) *
        (V * B ^ 2) =
      ((K : ZMod (p ^ 4)) ^ denominatorExponent m * V) *
        B ^ 2 * Q := by ring
    _ = B ^ 2 * (K : ZMod (p ^ 4)) ^ numeratorExponent m * Q := by
      rw [hcancel]
      ring

/-- The common numerator is the common denominator times the modular sum. -/
theorem generalizedCommonNumerator_cast_eq {m : ℤ} {p : ℕ}
    [Fact p.Prime] :
    (generalizedCommonNumerator m p : ZMod (p ^ 4)) =
      (generalizedCommonDen m p : ZMod (p ^ 4)) *
        generalizedBinomialSumMod m p 4 := by
  rw [generalizedCommonNumerator, generalizedBinomialSumMod,
    Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  simpa only [Nat.cast_mul, Nat.cast_pow] using
    (generalizedCommonDen_mul_binomial_summand k).symm

/-- The common numerator vanishes outside the exceptional set. -/
theorem generalizedCommonNumerator_cast_eq_zero_of_not_mem
    {m : ℤ} {p : ℕ} [Fact p.Prime]
    (hpnot : p ∉ exceptionalPrimes m) :
    (generalizedCommonNumerator m p : ZMod (p ^ 4)) = 0 := by
  rw [generalizedCommonNumerator_cast_eq,
    generalizedBinomialSumMod_eq_zero_of_not_mem hpnot, mul_zero]

/-- The common denominator is a unit modulo p⁴. -/
lemma generalizedCommonDen_isUnit {m : ℤ} {p : ℕ} [Fact p.Prime] :
    IsUnit (generalizedCommonDen m p : ZMod (p ^ 4)) := by
  rw [ZMod.isUnit_iff_coprime, generalizedCommonDen]
  have hlt : p - 1 < p :=
    Nat.sub_lt (show p.Prime from Fact.out).pos (by norm_num)
  exact
    (((show p.Prime from Fact.out).coprime_factorial_of_lt hlt).symm).pow
      (denominatorExponent m) 4

/-- Outside the exceptional set, p⁴ divides the reduced numerator. -/
theorem u_prime_sub_one_dvd_of_not_mem
    {m : ℤ} {p : ℕ} [Fact p.Prime]
    (hpnot : p ∉ exceptionalPrimes m) :
    ((p ^ 4 : ℕ) : ℤ) ∣ u m (p - 1) := by
  let q := generalizedSum m (p - 1)
  let N := generalizedCommonNumerator m p
  let D := generalizedCommonDen m p
  have hqdf : q = Rat.divInt (N : ℤ) (D : ℤ) := by
    rw [Rat.divInt_eq_div]
    exact generalizedSum_eq_commonNumerator_div m p
  have hDnat : D ≠ 0 := by
    dsimp [D, generalizedCommonDen]
    exact pow_ne_zero _ (Nat.factorial_ne_zero _)
  have hDint : (D : ℤ) ≠ 0 := by
    exact_mod_cast hDnat
  rcases Rat.num_den_mk hDint hqdf with ⟨c, hN, hD⟩
  have hNcast := congrArg
    (fun z : ℤ => (z : ZMod (p ^ 4))) hN
  simp only [Int.cast_natCast, Int.cast_mul] at hNcast
  have hDcast := congrArg
    (fun z : ℤ => (z : ZMod (p ^ 4))) hD
  simp only [Int.cast_natCast, Int.cast_mul] at hDcast
  have hNzero : (N : ZMod (p ^ 4)) = 0 := by
    exact generalizedCommonNumerator_cast_eq_zero_of_not_mem hpnot
  have hDunit : IsUnit (D : ZMod (p ^ 4)) := by
    exact generalizedCommonDen_isUnit
  have hprod :
      IsUnit ((c : ZMod (p ^ 4)) * (q.den : ZMod (p ^ 4))) := by
    rw [← hDcast]
    exact hDunit
  have hcunit : IsUnit (c : ZMod (p ^ 4)) :=
    (IsUnit.mul_iff.mp hprod).1
  have hu0 : (u m (p - 1) : ZMod (p ^ 4)) = 0 := by
    apply hcunit.mul_left_cancel
    calc
      (c : ZMod (p ^ 4)) * (u m (p - 1) : ZMod (p ^ 4)) =
          (N : ZMod (p ^ 4)) := by
            exact hNcast.symm
      _ = 0 := hNzero
      _ = (c : ZMod (p ^ 4)) * 0 := by ring
  exact
    (ZMod.intCast_zmod_eq_zero_iff_dvd (u m (p - 1)) (p ^ 4)).mp hu0

/-- The divisibility criterion stated without the exceptional set. -/
theorem u_prime_sub_one_dvd_of_good
    {m : ℤ} {p : ℕ} [Fact p.Prime]
    (hgood :
      (¬ ((p - 1 : ℕ) : ℤ) ∣ 2 * m + 4) ∨
        (p : ℤ) ∣ 2 * m + 7) :
    ((p ^ 4 : ℕ) : ℤ) ∣ u m (p - 1) := by
  apply u_prime_sub_one_dvd_of_not_mem
  intro hmem
  rw [mem_exceptionalPrimes_iff] at hmem
  rcases hgood with hnot | hcoeff
  · exact hnot hmem.2.1
  · exact hmem.2.2 hcoeff

end OddExponentCongruence
