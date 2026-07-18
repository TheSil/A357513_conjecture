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

For m ≥ 0, let u m n be the reduced numerator of
sum k = 1, ..., n, k ^ (-(2*m+1)) * choose(n,k)^2 * choose(n+k,k)^2.
The file proves that p ^ 4 ∣ u m (p - 1) for every prime outside
the explicit finite exceptional set exceptionalPrimes m.

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

/-- The generalized harmonic sum over \`1, ..., p - 1\` in \`ZMod m\`. -/
def harmonicMod (p m r : ℕ) : ZMod m :=
  ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod m)⁻¹) ^ r

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

/--
The pointwise expansion
\`(p - k)⁻⁵ = -k⁻⁵ - 5 p k⁻⁶\` in \`ZMod (p²)\`.
-/
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

/-! ## The odd-exponent generalization -/

/--
The rational sum with denominator exponent `2m+1`.  The lower endpoint is
`1`: the informal version with a `k = 0` term is undefined.
-/
def generalizedSum (m n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 n,
    ((n.choose k : ℚ) ^ 2 * ((n + k).choose k : ℚ) ^ 2) /
      (k : ℚ) ^ (2 * m + 1)

/-- The reduced numerator of `generalizedSum m n`. -/
def u (m n : ℕ) : ℤ := (generalizedSum m n).num

/-- The corresponding binomial sum in an arbitrary residue ring. -/
def generalizedBinomialSumMod (m p modulus : ℕ) : ZMod modulus :=
  ∑ k ∈ Finset.Icc 1 (p - 1),
    ((k : ZMod modulus)⁻¹) ^ (2 * m + 1) *
      (binomialProduct p k modulus) ^ 2

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

/-- Ring-theoretic core of the generalized summand reduction. -/
lemma generalized_summand_algebra {R : Type*} [CommRing R]
    (P U s C : R) (d : ℕ)
    (hs : s ^ 2 = 1) (hPC : P ^ 2 * C ^ 2 = P ^ 2)
    (hP4 : P ^ 4 = 0) :
    U ^ d * (s * P * U * (1 - P * U) * C) ^ 2 =
      P ^ 2 * U ^ (d + 2) - 2 * P ^ 3 * U ^ (d + 3) := by
  calc
    U ^ d * (s * P * U * (1 - P * U) * C) ^ 2 =
        (s ^ 2) * (P ^ 2 * C ^ 2) * (U ^ d * U ^ 2) *
          (1 - P * U) ^ 2 := by ring
    _ = P ^ 2 * U ^ (d + 2) * (1 - P * U) ^ 2 := by
      rw [hs, hPC, one_mul, ← pow_add]
    _ = P ^ 2 * U ^ (d + 2) - 2 * P ^ 3 * U ^ (d + 3) +
          P ^ 4 * U ^ (d + 4) := by
      rw [show d + 3 = (d + 2) + 1 by omega,
        show d + 4 = (d + 2) + 2 by omega, pow_succ, pow_add]
      ring
    _ = P ^ 2 * U ^ (d + 2) - 2 * P ^ 3 * U ^ (d + 3) := by
      rw [hP4, zero_mul, add_zero]

/-- A generalized summand, reduced modulo `p⁴`. -/
lemma generalized_binomial_summand_reduction {m p k : ℕ} [Fact p.Prime]
    (hk : k ∈ Finset.Icc 1 (p - 1)) :
    ((k : ZMod (p ^ 4))⁻¹) ^ (2 * m + 1) *
        (binomialProduct p k (p ^ 4)) ^ 2 =
      (p : ZMod (p ^ 4)) ^ 2 *
          ((k : ZMod (p ^ 4))⁻¹) ^ (2 * m + 3) -
        2 * (p : ZMod (p ^ 4)) ^ 3 *
          ((k : ZMod (p ^ 4))⁻¹) ^ (2 * m + 4) := by
  let P : ZMod (p ^ 4) := p
  let U : ZMod (p ^ 4) := (k : ZMod (p ^ 4))⁻¹
  let C : ZMod (p ^ 4) := correctionProd p k (p ^ 4)
  have hP4 : P ^ 4 = 0 := by
    dsimp [P]
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hsign : ((-1 : ZMod (p ^ 4)) ^ k) ^ 2 = 1 := by
    calc
      ((-1 : ZMod (p ^ 4)) ^ k) ^ 2 =
          (-1 : ZMod (p ^ 4)) ^ (k * 2) := (pow_mul _ _ _).symm
      _ = (-1 : ZMod (p ^ 4)) ^ (2 * k) := by rw [Nat.mul_comm]
      _ = ((-1 : ZMod (p ^ 4)) ^ 2) ^ k := pow_mul _ _ _
      _ = 1 := by norm_num
  rcases correctionProd_eq_one_add p k with ⟨T, hCraw⟩
  have hC : C = 1 + P ^ 2 * T := hCraw
  have hPC : P ^ 2 * C ^ 2 = P ^ 2 := by
    rw [hC]
    calc
      P ^ 2 * (1 + P ^ 2 * T) ^ 2 =
          P ^ 2 + P ^ 4 * (2 * T + P ^ 2 * T ^ 2) := by ring
      _ = P ^ 2 := by rw [hP4]; ring
  rw [binomialProduct_eq_closed hk, binomialClosed]
  change
    U ^ (2 * m + 1) *
        (((-1 : ZMod (p ^ 4)) ^ k * P * U * (1 - P * U) * C) ^ 2) =
      P ^ 2 * U ^ (2 * m + 3) - 2 * P ^ 3 * U ^ (2 * m + 4)
  simpa only [show 2 * m + 1 + 2 = 2 * m + 3 by omega,
      show 2 * m + 1 + 3 = 2 * m + 4 by omega] using
    generalized_summand_algebra P U ((-1 : ZMod (p ^ 4)) ^ k) C
      (2 * m + 1) hsign hPC hP4

/-- Summing the pointwise reduction gives two generalized harmonic sums. -/
theorem generalizedBinomialSumMod_reduction {m p : ℕ} [Fact p.Prime] :
    generalizedBinomialSumMod m p (p ^ 4) =
      (p : ZMod (p ^ 4)) ^ 2 * harmonicMod p (p ^ 4) (2 * m + 3) -
        2 * (p : ZMod (p ^ 4)) ^ 3 *
          harmonicMod p (p ^ 4) (2 * m + 4) := by
  rw [generalizedBinomialSumMod, harmonicMod]
  calc
    (∑ k ∈ Finset.Icc 1 (p - 1),
        ((k : ZMod (p ^ 4))⁻¹) ^ (2 * m + 1) *
          (binomialProduct p k (p ^ 4)) ^ 2) =
      ∑ k ∈ Finset.Icc 1 (p - 1),
        ((p : ZMod (p ^ 4)) ^ 2 *
            ((k : ZMod (p ^ 4))⁻¹) ^ (2 * m + 3) -
          2 * (p : ZMod (p ^ 4)) ^ 3 *
            ((k : ZMod (p ^ 4))⁻¹) ^ (2 * m + 4)) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact generalized_binomial_summand_reduction hk
    _ = (p : ZMod (p ^ 4)) ^ 2 *
          (∑ k ∈ Finset.Icc 1 (p - 1),
            ((k : ZMod (p ^ 4))⁻¹) ^ (2 * m + 3)) -
        2 * (p : ZMod (p ^ 4)) ^ 3 *
          (∑ k ∈ Finset.Icc 1 (p - 1),
            ((k : ZMod (p ^ 4))⁻¹) ^ (2 * m + 4)) := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
                ← Finset.mul_sum]

/-! ### Generalized harmonic pairing -/

/-- First-order expansion of an arbitrary odd power. -/
lemma odd_power_first_order {R : Type*} [CommRing R]
    (P U : R) (m : ℕ) (hP2 : P ^ 2 = 0) :
    (-U - P * U ^ 2) ^ (2 * m + 3) =
      -U ^ (2 * m + 3) -
        ((2 * m + 3 : ℕ) : R) * P * U ^ (2 * m + 4) := by
  have hx : (P * U) ^ 2 = 0 := by
    rw [mul_pow, hP2, zero_mul]
  have hsign : (-1 : R) ^ (2 * m + 3) = -1 := by
    rw [show 2 * m + 3 = 2 * (m + 1) + 1 by omega,
      pow_succ, pow_mul]
    norm_num
  calc
    (-U - P * U ^ 2) ^ (2 * m + 3) =
        ((-U) * (1 + P * U)) ^ (2 * m + 3) := by
          congr 1
          ring
    _ = (-U) ^ (2 * m + 3) * (1 + P * U) ^ (2 * m + 3) := by
          rw [mul_pow]
    _ = -U ^ (2 * m + 3) *
          (1 + ((2 * m + 3 : ℕ) : R) * (P * U)) := by
          rw [one_add_pow_of_sq_eq_zero (P * U) (2 * m + 3) hx]
          rw [neg_pow, hsign]
          ring
    _ = -U ^ (2 * m + 3) -
        ((2 * m + 3 : ℕ) : R) * P * U ^ (2 * m + 4) := by
          rw [show 2 * m + 4 = (2 * m + 3) + 1 by omega, pow_succ]
          ring

/-- The pointwise reflection formula in `ZMod (p²)`. -/
lemma paired_inverse_odd {m p k : ℕ} [Fact p.Prime]
    (hk : k ∈ Finset.Icc 1 (p - 1)) :
    (((p - k : ℕ) : ZMod (p ^ 2))⁻¹) ^ (2 * m + 3) =
      -((k : ZMod (p ^ 2))⁻¹) ^ (2 * m + 3) -
        ((2 * m + 3 : ℕ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
          ((k : ZMod (p ^ 2))⁻¹) ^ (2 * m + 4) := by
  let P : ZMod (p ^ 2) := p
  let K : ZMod (p ^ 2) := k
  let U : ZMod (p ^ 2) := K⁻¹
  have hk_bounds := Finset.mem_Icc.mp hk
  have hk_le : k ≤ p := by omega
  have hk_unit : IsUnit K := by
    rw [ZMod.isUnit_iff_coprime]
    exact (mem_Icc_coprime_prime hk).pow_right 2
  have hP2 : P ^ 2 = 0 := by
    dsimp [P]
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hKU : K * U = 1 := ZMod.mul_inv_of_unit K hk_unit
  have hcast : ((p - k : ℕ) : ZMod (p ^ 2)) = P - K := by
    dsimp [P, K]
    rw [Nat.cast_sub hk_le]
  have hinv : ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ = -U - P * U ^ 2 := by
    apply ZMod.inv_eq_of_mul_eq_one
    rw [hcast]
    calc
      (P - K) * (-U - P * U ^ 2)
          = K * U + P * U * (K * U - 1) - P ^ 2 * U ^ 2 := by ring
      _ = 1 := by rw [hKU, hP2]; ring
  rw [hinv]
  exact odd_power_first_order P U m hP2

/-- Pairing `k` with `p-k` for every exponent `2m+3`. -/
lemma harmonic_pairing_odd {m p : ℕ} [Fact p.Prime] :
    2 * harmonicMod p (p ^ 2) (2 * m + 3) =
      -((2 * m + 3 : ℕ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
        harmonicMod p (p ^ 2) (2 * m + 4) := by
  let s := Finset.Icc 1 (p - 1)
  have hperm :
      (∑ k ∈ s,
        ((((p - k : ℕ) : ZMod (p ^ 2))⁻¹) ^ (2 * m + 3))) =
        harmonicMod p (p ^ 2) (2 * m + 3) := by
    rw [harmonicMod, Finset.sum_subtype s (fun _ => Iff.rfl)]
    rw [Finset.sum_subtype s (fun _ => Iff.rfl)]
    apply Fintype.sum_equiv (reflectionEquiv p)
    intro k
    rfl
  have hrel :
      harmonicMod p (p ^ 2) (2 * m + 3) =
        -harmonicMod p (p ^ 2) (2 * m + 3) -
          ((2 * m + 3 : ℕ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
            harmonicMod p (p ^ 2) (2 * m + 4) := by
    calc
      harmonicMod p (p ^ 2) (2 * m + 3) =
          ∑ k ∈ s, ((((p - k : ℕ) : ZMod (p ^ 2))⁻¹) ^
            (2 * m + 3)) := hperm.symm
      _ = ∑ k ∈ s,
          (-((k : ZMod (p ^ 2))⁻¹) ^ (2 * m + 3) -
            ((2 * m + 3 : ℕ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
              ((k : ZMod (p ^ 2))⁻¹) ^ (2 * m + 4)) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact paired_inverse_odd hk
      _ = -harmonicMod p (p ^ 2) (2 * m + 3) -
          ((2 * m + 3 : ℕ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
            harmonicMod p (p ^ 2) (2 * m + 4) := by
          simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
          rw [← Finset.mul_sum]
          rfl
  calc
    2 * harmonicMod p (p ^ 2) (2 * m + 3) =
        harmonicMod p (p ^ 2) (2 * m + 3) +
          harmonicMod p (p ^ 2) (2 * m + 3) := by ring
    _ = harmonicMod p (p ^ 2) (2 * m + 3) +
        (-harmonicMod p (p ^ 2) (2 * m + 3) -
          ((2 * m + 3 : ℕ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
            harmonicMod p (p ^ 2) (2 * m + 4)) :=
      congrArg (fun x => harmonicMod p (p ^ 2) (2 * m + 3) + x) hrel
    _ = -((2 * m + 3 : ℕ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
        harmonicMod p (p ^ 2) (2 * m + 4) := by ring

/-- Vanishing modulo `p²` can be lifted after multiplication by `p²`. -/
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

/-- Reduction from `p⁴` to `p²` preserves the relevant inverses. -/
lemma castHom_inverse_Icc_sq {p k : ℕ} [Fact p.Prime]
    (hk : k ∈ Finset.Icc 1 (p - 1)) :
    (ZMod.castHom
      (show p ^ 2 ∣ p ^ 4 by
        use p ^ 2
        ring)
      (ZMod (p ^ 2))) (((k : ZMod (p ^ 4))⁻¹)) =
        ((k : ZMod (p ^ 2))⁻¹) := by
  let f : ZMod (p ^ 4) →+* ZMod (p ^ 2) :=
    ZMod.castHom
      (show p ^ 2 ∣ p ^ 4 by
        use p ^ 2
        ring)
      (ZMod (p ^ 2))
  have hku : IsUnit (k : ZMod (p ^ 4)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (mem_Icc_coprime_prime hk).pow_right 4
  symm
  apply ZMod.inv_eq_of_mul_eq_one
  calc
    (k : ZMod (p ^ 2)) * f (((k : ZMod (p ^ 4))⁻¹)) =
        f (k : ZMod (p ^ 4)) * f (((k : ZMod (p ^ 4))⁻¹)) := by
          rw [map_natCast]
    _ = f ((k : ZMod (p ^ 4)) * ((k : ZMod (p ^ 4))⁻¹)) := by
      rw [map_mul]
    _ = f 1 := by rw [ZMod.mul_inv_of_unit _ hku]
    _ = 1 := by rw [map_one]

/-- Generalized harmonic sums commute with reduction from `p⁴` to `p²`. -/
lemma castHom_harmonic_sq {p r : ℕ} [Fact p.Prime] :
    (ZMod.castHom
      (show p ^ 2 ∣ p ^ 4 by
        use p ^ 2
        ring)
      (ZMod (p ^ 2))) (harmonicMod p (p ^ 4) r) =
        harmonicMod p (p ^ 2) r := by
  simp only [harmonicMod, map_sum, map_pow]
  apply Finset.sum_congr rfl
  intro k hk
  rw [castHom_inverse_Icc_sq hk]

/-- The generalized pairing relation at modulus `p⁴`, with its factor `p²`. -/
theorem generalized_harmonic_pairing_mul_p_sq {m p : ℕ} [Fact p.Prime] :
    (p : ZMod (p ^ 4)) ^ 2 *
      (2 * harmonicMod p (p ^ 4) (2 * m + 3) +
        ((2 * m + 3 : ℕ) : ZMod (p ^ 4)) * (p : ZMod (p ^ 4)) *
          harmonicMod p (p ^ 4) (2 * m + 4)) = 0 := by
  apply mul_p_sq_eq_zero_of_cast_eq_zero
  simp only [map_add, map_mul, map_natCast, map_ofNat, castHom_harmonic_sq]
  rw [harmonic_pairing_odd]
  ring

/-- The coefficient form of the key reduction, valid for all odd exponents. -/
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

/--
The central generalized congruence:
`2S = -(2m+7)p³ H_(2m+4)` in `ZMod (p⁴)`.
-/
theorem generalized_key_congruence {m p : ℕ} [Fact p.Prime] :
    2 * generalizedBinomialSumMod m p (p ^ 4) =
      -((2 * m + 7 : ℕ) : ZMod (p ^ 4)) *
        (p : ZMod (p ^ 4)) ^ 3 *
          harmonicMod p (p ^ 4) (2 * m + 4) := by
  let P : ZMod (p ^ 4) := p
  let Hr := harmonicMod p (p ^ 4) (2 * m + 3)
  let He := harmonicMod p (p ^ 4) (2 * m + 4)
  let S := generalizedBinomialSumMod m p (p ^ 4)
  have hS : S = P ^ 2 * Hr - 2 * P ^ 3 * He :=
    generalizedBinomialSumMod_reduction
  have hH :
      P ^ 2 *
        (2 * Hr + ((2 * m + 3 : ℕ) : ZMod (p ^ 4)) * P * He) = 0 :=
    generalized_harmonic_pairing_mul_p_sq
  have hkey := key_reduction_scaled_general P Hr He S
    (((2 * m + 3 : ℕ) : ZMod (p ^ 4))) hS hH
  dsimp [S, P, He] at hkey ⊢
  convert hkey using 1
  all_goals
    push_cast
    ring

/-! ### The finite exceptional set -/

/-- Rewrite an arbitrary inverse-power sum as a sum over the unit group. -/
lemma sum_Icc_inverse_pow_eq_units (p e : ℕ) [Fact p.Prime] :
    (∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ e) =
      ∑ x : (ZMod p)ˣ, ((x : ZMod p)⁻¹) ^ e := by
  rw [Finset.sum_subtype (Finset.Icc 1 (p - 1)) (fun _ => Iff.rfl)]
  apply Fintype.sum_equiv (residueUnitEquiv p)
  intro k
  change ((k.1 : ZMod p)⁻¹) ^ e =
    (((ZMod.unitOfCoprime k.1 (mem_Icc_coprime_prime k.2) : (ZMod p)ˣ) :
      ZMod p)⁻¹) ^ e
  rw [ZMod.coe_unitOfCoprime]

/-- Inversion permutes the units for every exponent. -/
lemma sum_inverse_powers_units (p e : ℕ) [Fact p.Prime] :
    (∑ x : (ZMod p)ˣ, ((x : ZMod p)⁻¹) ^ e) =
      ∑ x : (ZMod p)ˣ, (x : ZMod p) ^ e := by
  apply Fintype.sum_equiv (Equiv.inv ((ZMod p)ˣ))
  intro x
  simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val]

/-- A power sum over the units vanishes unless the group order divides
the exponent. -/
theorem sum_powers_units_eq_zero_of_not_dvd {p e : ℕ} [Fact p.Prime]
    (hnot : ¬ p - 1 ∣ e) :
    (∑ x : (ZMod p)ˣ, ((x : (ZMod p)ˣ) : ZMod p) ^ e) = 0 := by
  rw [FiniteField.sum_pow_units]
  simp only [ZMod.card, hnot, ↓reduceIte]

/-- The corresponding generalized harmonic sum vanishes modulo `p`. -/
theorem harmonic_eq_zero_mod_prime {p e : ℕ} [Fact p.Prime]
    (hnot : ¬ p - 1 ∣ e) :
    harmonicMod p p e = 0 := by
  rw [harmonicMod, sum_Icc_inverse_pow_eq_units,
    sum_inverse_powers_units]
  exact sum_powers_units_eq_zero_of_not_dvd hnot

/-- Reduction from `p⁴` to `p` commutes with every harmonic sum. -/
lemma castHom_harmonic {p e : ℕ} [Fact p.Prime] :
    (ZMod.castHom (show p ∣ p ^ 4 by exact dvd_pow_self p (by norm_num))
      (ZMod p)) (harmonicMod p (p ^ 4) e) =
        harmonicMod p p e := by
  simp only [harmonicMod, map_sum, map_pow]
  apply Finset.sum_congr rfl
  intro k hk
  rw [castHom_inverse_Icc hk]

/-- Finite-field vanishing lifted to `ZMod (p⁴)`. -/
theorem harmonic_mul_p_cube_eq_zero_of_not_dvd {p e : ℕ} [Fact p.Prime]
    (hnot : ¬ p - 1 ∣ e) :
    (p : ZMod (p ^ 4)) ^ 3 * harmonicMod p (p ^ 4) e = 0 := by
  apply mul_p_cube_eq_zero_of_cast_eq_zero
  rw [castHom_harmonic]
  exact harmonic_eq_zero_mod_prime hnot

/-- If `p` divides a coefficient, that coefficient times `p³` vanishes
modulo `p⁴`. -/
lemma coefficient_mul_p_cube_eq_zero_of_dvd {p c : ℕ}
    (hpc : p ∣ c) (x : ZMod (p ^ 4)) :
    ((c : ℕ) : ZMod (p ^ 4)) * (p : ZMod (p ^ 4)) ^ 3 * x = 0 := by
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

/-- Two is a unit modulo `p⁴` for every odd prime `p`. -/
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

/--
The generalized modular sum vanishes whenever either the group-order
obstruction is absent or the coefficient `2m+7` supplies an extra factor
of `p`.
-/
theorem generalizedBinomialSumMod_eq_zero {m p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2)
    (hgood : (¬ p - 1 ∣ 2 * m + 4) ∨ p ∣ 2 * m + 7) :
    generalizedBinomialSumMod m p (p ^ 4) = 0 := by
  let P : ZMod (p ^ 4) := p
  let H := harmonicMod p (p ^ 4) (2 * m + 4)
  let S := generalizedBinomialSumMod m p (p ^ 4)
  have hright :
      ((2 * m + 7 : ℕ) : ZMod (p ^ 4)) * P ^ 3 * H = 0 := by
    rcases hgood with hnot | hdiv
    · have hH : P ^ 3 * H = 0 :=
        harmonic_mul_p_cube_eq_zero_of_not_dvd hnot
      calc
        ((2 * m + 7 : ℕ) : ZMod (p ^ 4)) * P ^ 3 * H =
            ((2 * m + 7 : ℕ) : ZMod (p ^ 4)) * (P ^ 3 * H) := by ring
        _ = 0 := by rw [hH, mul_zero]
    · exact coefficient_mul_p_cube_eq_zero_of_dvd hdiv H
  have h2 : IsUnit (2 : ZMod (p ^ 4)) :=
    two_isUnit_mod_prime_four hp2
  apply h2.mul_left_cancel
  calc
    2 * S =
        -((2 * m + 7 : ℕ) : ZMod (p ^ 4)) * P ^ 3 * H :=
      generalized_key_congruence
    _ = -(((2 * m + 7 : ℕ) : ZMod (p ^ 4)) * P ^ 3 * H) := by ring
    _ = 0 := by rw [hright, neg_zero]
    _ = 2 * 0 := by ring

/--
The exceptional primes are stored in a finite range.  Their defining
condition is `p-1 ∣ 2m+4` but `p ∤ 2m+7`.
-/
def exceptionalPrimes (m : ℕ) : Finset ℕ :=
  (Finset.range (2 * m + 6)).filter fun p =>
    p.Prime ∧ p - 1 ∣ 2 * m + 4 ∧ ¬ p ∣ 2 * m + 7

theorem mem_exceptionalPrimes_iff {m p : ℕ} :
    p ∈ exceptionalPrimes m ↔
      p.Prime ∧ p - 1 ∣ 2 * m + 4 ∧ ¬ p ∣ 2 * m + 7 := by
  rw [exceptionalPrimes, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have hsub : p - 1 ≤ 2 * m + 4 :=
      Nat.le_of_dvd (by omega) h.2.1
    have hp1 : 1 ≤ p := h.1.one_le
    omega

/-- Every prime outside `exceptionalPrimes m` has vanishing modular sum. -/
theorem generalizedBinomialSumMod_eq_zero_of_not_mem
    {m p : ℕ} [Fact p.Prime] (hpnot : p ∉ exceptionalPrimes m) :
    generalizedBinomialSumMod m p (p ^ 4) = 0 := by
  have hp2 : p ≠ 2 := by
    intro hp
    subst p
    apply hpnot
    rw [mem_exceptionalPrimes_iff]
    refine ⟨Nat.prime_two, by norm_num, ?_⟩
    intro hdiv
    rcases hdiv with ⟨q, hq⟩
    omega
  have hgood : (¬ p - 1 ∣ 2 * m + 4) ∨ p ∣ 2 * m + 7 := by
    by_cases hdiv : p - 1 ∣ 2 * m + 4
    · right
      by_contra hcoeff
      apply hpnot
      rw [mem_exceptionalPrimes_iff]
      exact ⟨Fact.out, hdiv, hcoeff⟩
    · exact Or.inl hdiv
  exact generalizedBinomialSumMod_eq_zero hp2 hgood

/-! ### Passage to the reduced rational numerator -/

/-- A common denominator for exponent `2m+1`. -/
def generalizedCommonDen (m p : ℕ) : ℕ :=
  (Nat.factorial (p - 1)) ^ (2 * m + 1)

/-- The numerator before cancellation of the generalized common denominator. -/
def generalizedCommonNumerator (m p : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 (p - 1),
    (((p - 1).choose k * (p - 1 + k).choose k) ^ 2) *
      (generalizedCommonDen m p / k ^ (2 * m + 1))

/-- Each denominator power divides the generalized common denominator. -/
lemma odd_power_dvd_generalizedCommonDen {m p k : ℕ}
    (hk : k ∈ Finset.Icc 1 (p - 1)) :
    k ^ (2 * m + 1) ∣ generalizedCommonDen m p := by
  rw [generalizedCommonDen]
  exact pow_dvd_pow_of_dvd
    (Nat.dvd_factorial (Finset.mem_Icc.mp hk).1
      (Finset.mem_Icc.mp hk).2) (2 * m + 1)

/-- One generalized rational summand over the explicit common denominator. -/
lemma generalized_rational_summand_eq_commonDen {m p k : ℕ}
    (hk : k ∈ Finset.Icc 1 (p - 1)) :
    (((p - 1).choose k : ℚ) ^ 2 *
        ((p - 1 + k).choose k : ℚ) ^ 2) /
          (k : ℚ) ^ (2 * m + 1) =
      ((((p - 1).choose k * (p - 1 + k).choose k) ^ 2 *
          (generalizedCommonDen m p / k ^ (2 * m + 1)) : ℕ) : ℚ) /
        (generalizedCommonDen m p : ℚ) := by
  have hk0 : k ≠ 0 := by
    have := (Finset.mem_Icc.mp hk).1
    omega
  have hD0 : generalizedCommonDen m p ≠ 0 := by
    rw [generalizedCommonDen]
    exact pow_ne_zero (2 * m + 1) (Nat.factorial_ne_zero _)
  have hmul :=
    Nat.mul_div_cancel'
      (odd_power_dvd_generalizedCommonDen (m := m) hk)
  have hDq :
      (generalizedCommonDen m p : ℚ) =
        (k : ℚ) ^ (2 * m + 1) *
          (generalizedCommonDen m p / k ^ (2 * m + 1) : ℕ) := by
    exact_mod_cast hmul.symm
  field_simp [hk0, hD0]
  rw [hDq]
  push_cast
  ring

/-- The generalized rational sum over its explicit common denominator. -/
theorem generalizedSum_eq_commonNumerator_div (m p : ℕ) :
    generalizedSum m (p - 1) =
      (generalizedCommonNumerator m p : ℚ) /
        (generalizedCommonDen m p : ℚ) := by
  rw [generalizedSum, generalizedCommonNumerator]
  calc
    (∑ k ∈ Finset.Icc 1 (p - 1),
        (((p - 1).choose k : ℚ) ^ 2 *
          ((p - 1 + k).choose k : ℚ) ^ 2) /
            (k : ℚ) ^ (2 * m + 1)) =
      ∑ k ∈ Finset.Icc 1 (p - 1),
        ((((p - 1).choose k * (p - 1 + k).choose k) ^ 2 *
          (generalizedCommonDen m p / k ^ (2 * m + 1)) : ℕ) : ℚ) /
            (generalizedCommonDen m p : ℚ) := by
              apply Finset.sum_congr rfl
              intro k hk
              exact generalized_rational_summand_eq_commonDen hk
    _ = (∑ k ∈ Finset.Icc 1 (p - 1),
          ((((p - 1).choose k * (p - 1 + k).choose k) ^ 2 *
            (generalizedCommonDen m p / k ^ (2 * m + 1)) : ℕ) : ℚ)) /
        (generalizedCommonDen m p : ℚ) := by
          simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = (((∑ k ∈ Finset.Icc 1 (p - 1),
          ((p - 1).choose k * (p - 1 + k).choose k) ^ 2 *
            (generalizedCommonDen m p / k ^ (2 * m + 1)) : ℕ) : ℚ)) /
        (generalizedCommonDen m p : ℚ) := by
          push_cast
          rfl

/-- Multiplication by the generalized denominator removes one modular
summand's inverse power. -/
lemma generalizedCommonDen_mul_binomial_summand
    {m p k : ℕ} [Fact p.Prime]
    (hk : k ∈ Finset.Icc 1 (p - 1)) :
    (generalizedCommonDen m p : ZMod (p ^ 4)) *
        (((k : ZMod (p ^ 4))⁻¹) ^ (2 * m + 1) *
          (binomialProduct p k (p ^ 4)) ^ 2) =
      ((((p - 1).choose k * (p - 1 + k).choose k) ^ 2 *
        (generalizedCommonDen m p / k ^ (2 * m + 1)) : ℕ) :
          ZMod (p ^ 4)) := by
  let K : ZMod (p ^ 4) := k
  let U : ZMod (p ^ 4) := K⁻¹
  let B : ZMod (p ^ 4) :=
    ((p - 1).choose k * (p - 1 + k).choose k : ℕ)
  let Q : ZMod (p ^ 4) :=
    (generalizedCommonDen m p / k ^ (2 * m + 1) : ℕ)
  have hku : IsUnit K := by
    rw [ZMod.isUnit_iff_coprime]
    exact (mem_Icc_coprime_prime hk).pow_right 4
  have hKU : K * U = 1 := ZMod.mul_inv_of_unit K hku
  have hmul :=
    Nat.mul_div_cancel'
      (odd_power_dvd_generalizedCommonDen (m := m) hk)
  have hDcast :
      (generalizedCommonDen m p : ZMod (p ^ 4)) =
        K ^ (2 * m + 1) * Q := by
    have hcast := congrArg
      (fun n : ℕ => (n : ZMod (p ^ 4))) hmul.symm
    simp only [Nat.cast_mul, Nat.cast_pow] at hcast
    exact hcast
  have hBcast :
      ((p - 1).choose k : ZMod (p ^ 4)) *
          ((p - 1 + k).choose k : ZMod (p ^ 4)) = B := by
    dsimp [B]
    push_cast
    rfl
  rw [binomialProduct, hBcast]
  change
    (generalizedCommonDen m p : ZMod (p ^ 4)) *
        (U ^ (2 * m + 1) * B ^ 2) =
      ((((p - 1).choose k * (p - 1 + k).choose k) ^ 2 *
        (generalizedCommonDen m p / k ^ (2 * m + 1)) : ℕ) :
          ZMod (p ^ 4))
  push_cast
  rw [hBcast]
  change
    (generalizedCommonDen m p : ZMod (p ^ 4)) *
      (U ^ (2 * m + 1) * B ^ 2) = B ^ 2 * Q
  rw [hDcast]
  calc
    K ^ (2 * m + 1) * Q * (U ^ (2 * m + 1) * B ^ 2) =
        (K * U) ^ (2 * m + 1) * B ^ 2 * Q := by
          rw [mul_pow]
          ring
    _ = B ^ 2 * Q := by rw [hKU]; ring

/-- The generalized common numerator is denominator times modular sum. -/
theorem generalizedCommonNumerator_cast_eq {m p : ℕ} [Fact p.Prime] :
    (generalizedCommonNumerator m p : ZMod (p ^ 4)) =
      (generalizedCommonDen m p : ZMod (p ^ 4)) *
        generalizedBinomialSumMod m p (p ^ 4) := by
  rw [generalizedCommonNumerator, generalizedBinomialSumMod,
    Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  simpa only [Nat.cast_mul, Nat.cast_pow] using
    (generalizedCommonDen_mul_binomial_summand hk).symm

/-- The explicit generalized numerator vanishes outside the exceptional set. -/
theorem generalizedCommonNumerator_cast_eq_zero_of_not_mem
    {m p : ℕ} [Fact p.Prime] (hpnot : p ∉ exceptionalPrimes m) :
    (generalizedCommonNumerator m p : ZMod (p ^ 4)) = 0 := by
  rw [generalizedCommonNumerator_cast_eq,
    generalizedBinomialSumMod_eq_zero_of_not_mem hpnot, mul_zero]

/-- The generalized common denominator is a unit modulo `p⁴`. -/
lemma generalizedCommonDen_isUnit {m p : ℕ} [Fact p.Prime] :
    IsUnit (generalizedCommonDen m p : ZMod (p ^ 4)) := by
  rw [ZMod.isUnit_iff_coprime, generalizedCommonDen]
  have hlt : p - 1 < p :=
    Nat.sub_lt (show p.Prime from Fact.out).pos (by norm_num)
  exact
    (((show p.Prime from Fact.out).coprime_factorial_of_lt hlt).symm).pow
      (2 * m + 1) 4

/--
For every prime outside the explicit finite exceptional set, `p⁴` divides
the reduced numerator `u m (p-1)`.
-/
theorem u_prime_sub_one_dvd_of_not_mem
    {m p : ℕ} [Fact p.Prime] (hpnot : p ∉ exceptionalPrimes m) :
    ((p ^ 4 : ℕ) : ℤ) ∣ u m (p - 1) := by
  let q := generalizedSum m (p - 1)
  let N := generalizedCommonNumerator m p
  let D := generalizedCommonDen m p
  have hqdf : q = Rat.divInt (N : ℤ) (D : ℤ) := by
    rw [Rat.divInt_eq_div]
    exact generalizedSum_eq_commonNumerator_div m p
  have hDnat : D ≠ 0 := by
    dsimp [D, generalizedCommonDen]
    exact pow_ne_zero (2 * m + 1) (Nat.factorial_ne_zero _)
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

/--
Equivalent criterion without mentioning the finite set explicitly.
-/
theorem u_prime_sub_one_dvd_of_good
    {m p : ℕ} [Fact p.Prime]
    (hgood : (¬ p - 1 ∣ 2 * m + 4) ∨ p ∣ 2 * m + 7) :
    ((p ^ 4 : ℕ) : ℤ) ∣ u m (p - 1) := by
  apply u_prime_sub_one_dvd_of_not_mem
  intro hmem
  rw [mem_exceptionalPrimes_iff] at hmem
  rcases hgood with hnot | hcoeff
  · exact hnot hmem.2.1
  · exact hmem.2.2 hcoeff

end OddExponentCongruence
