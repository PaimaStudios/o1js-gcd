import { Bool, Field, Gadgets, Provable, Struct, provable } from 'o1js';

enum Ordering {
  Less,
  Equal,
  Greater,
}

// Increase this to make Bigint2048 bigger.
const LIMB_NUM = 18;

const Limbs = Provable.Array(Field, LIMB_NUM);

// Should be kept less than half of Mina's 254 to make carry easy to handle.
const LIMB_BITS = 116n;
const MODULUS = 1n << LIMB_BITS;
const MASK = MODULUS - 1n;

/** Escape from Provable context to be allowed to format an error message. */
function errorMessage(x: () => string): string {
  let s = '';
  Provable.asProver(() => (s = x()));
  return s;
}

/**
 * We use LIMB_BITS-bit limbs, which means LIMB_NUM limbs for numbers as used in RSA.
 */
const Field18 = Provable.Array(Field, LIMB_NUM);

export class Bigint2048 extends Struct({
  negative: Bool,
  fields: Field18,
}) {
  static from(x: bigint) {
    const negative = x < 0n;
    if (negative) {
      x = -x;
    }
    let fields = [];
    for (let i = 0; i < LIMB_NUM; i++) {
      fields.push(Field(x & MASK));
      x >>= LIMB_BITS;
    }
    if (x !== 0n) throw new Error('leftover: ' + x);
    return new Bigint2048({ negative: Bool(negative), fields });
  }

  static readonly MAX = Bigint2048.from(
    (1n << (LIMB_BITS * BigInt(LIMB_NUM))) - 1n
  );
  static readonly ZERO = Bigint2048.from(0n);
  static readonly ONE = Bigint2048.from(1n);

  static check(x: { fields: Field[] }) {
    for (let i = 0; i < LIMB_NUM; i++) {
      rangeCheck116(x.fields[i]);
    }
  }

  toBigInt(): bigint {
    let value = 0n;
    for (let i = LIMB_NUM - 1; i >= 0; i--) {
      value <<= BigInt(LIMB_BITS);
      value += this.fields[i].toBigInt();
    }
    if (this.negative.toBoolean()) {
      value = -value;
    }
    return value;
  }

  toString(): string {
    return `${this.toBigInt() == 0n && this.negative.toBoolean() ? '-' : ''}${this.toBigInt()}`;
  }

  toJSON(): string {
    return this.toString();
  }

  // --------------------------------------------------------------------------
  // Bit manipulation

  toBits(): Bool[] {
    const r = [];
    for (let i = 0; i < LIMB_NUM; i++) {
      r.push(...this.fields[i].toBits(Number(LIMB_BITS)));
    }
    return r;
  }

  // --------------------------------------------------------------------------
  // Bignum math

  abs(): Bigint2048 {
    return new Bigint2048({
      negative: Bool(false),
      fields: this.fields,
    });
  }

  neg(): Bigint2048 {
    return new Bigint2048({
      negative: this.negative.not(),
      fields: this.fields,
    });
  }

  modMul(x: Bigint2048, y: Bigint2048) {
    return multiply(x, y, this);
  }

  modSquare(x: Bigint2048) {
    return multiply(x, x, this, { isSquare: true });
  }

  add(rhs: Bigint2048): Bigint2048 {
    // same sign:
    //   X + y = x + y
    //   -x + -y = -(x + y)
    // different sign:
    //   Big - Small = +
    //   Small - Big = -
    //   -Big + Small = -
    //   -Small + Big = +
    const isSub = this.negative.equals(rhs.negative).not();
    const thisSmall = this.abs().lessThan(rhs.abs());
    const resultNegative = Provable.if(
      isSub,
      Bool,
      rhs.negative.equals(thisSmall),
      this.negative
    );

    const addFields = Limbs.empty();
    let carry = Bool(false);

    for (let i = 0; i < LIMB_NUM; i++) {
      addFields[i] = this.fields[i].add(rhs.fields[i]).add(carry.toField());
      carry = addFields[i].greaterThan(MASK);
      addFields[i] = Provable.if(
        carry,
        Field,
        addFields[i].sub(MODULUS),
        addFields[i]
      );
    }
    carry.assertFalse();

    const [bigger, smaller] = Provable.if(
      thisSmall,
      Provable.Array(Bigint2048, 2),
      [rhs, this],
      [this, rhs]
    );
    const subFields = Limbs.empty();
    carry = Bool(false);
    for (let i = 0; i < LIMB_NUM; i++) {
      subFields[i] = bigger.fields[i]
        .sub(smaller.fields[i])
        .sub(carry.toField());
      carry = subFields[i].greaterThan(MASK);
      subFields[i] = Provable.if(
        carry,
        Field,
        subFields[i].add(MODULUS),
        subFields[i]
      );
    }
    carry.assertFalse();

    const fields = Provable.if(isSub, Limbs, subFields, addFields);
    return new Bigint2048({
      negative: resultNegative,
      fields,
    });
  }

  sub(y: Bigint2048): Bigint2048 {
    return this.add(y.neg());
  }

  mul(y: Bigint2048): Bigint2048 {
    return new Bigint2048({
      negative: this.negative.equals(y.negative).not(),
      fields: Bigint2048.MAX.modMul(this.abs(), y.abs()).fields,
    });
  }

  square(): Bigint2048 {
    return Bigint2048.MAX.modSquare(this.abs());
  }

  /** Remainder will have the same sign as `y`. */
  floorDiv(y: Bigint2048): { quot: Bigint2048; rem: Bigint2048 } {
    y.assertNotEquals(Bigint2048.ZERO);

    // sign(r) = sign(y)
    const { q, r } = Provable.witness(
      Struct({ q: Bigint2048, r: Bigint2048 }),
      () => {
        let lhs = this.toBigInt(),
          rhs = y.toBigInt(),
          q = lhs / rhs,
          r = lhs % rhs;
        if (r != 0n && r < 0n != rhs < 0n) {
          --q;
          r += rhs;
        }
        return { q: Bigint2048.from(q), r: Bigint2048.from(r) };
      }
    );

    // this = q * y + r
    y.mul(q).add(r).assertEquals(this);
    // abs(r) < abs(rhs)
    r.abs().assertLessThan(y.abs());
    // sign(r) = sign(rhs) for truncation
    r.equals(Bigint2048.ZERO).or(r.negative.equals(y.negative)).assertTrue();
    return { quot: q, rem: r };
  }

  /** Remainder will have the same sign as `this`. */
  truncDiv(y: Bigint2048): { quot: Bigint2048; rem: Bigint2048 } {
    y.assertNotEquals(Bigint2048.ZERO);

    const { q, r } = Provable.witness(
      Struct({ q: Bigint2048, r: Bigint2048 }),
      () => {
        let lhs = this.toBigInt(),
          rhs = y.toBigInt(),
          q = lhs / rhs,
          r = lhs % rhs;
        return { q: Bigint2048.from(q), r: Bigint2048.from(r) };
      }
    );

    // this = q * y + r
    y.mul(q).add(r).assertEquals(this);
    // sign(r) = sign(lhs) for truncation
    r.equals(Bigint2048.ZERO).or(r.negative.equals(this.negative)).assertTrue();
    // abs(r) < abs(rhs)
    r.abs().assertLessThan(y.abs());
    return { quot: q, rem: r };
  }

  divExact(y: Bigint2048): Bigint2048 {
    // this = q * y
    const q = Provable.witness(Bigint2048, () => {
      return Bigint2048.from(this.toBigInt() / y.toBigInt());
    });
    y.mul(q).assertEquals(this);
    return q;
  }

  powField(exponent: Field): Bigint2048 {
    const bits = exponent.toBits();
    let result = Bigint2048.from(1n);
    // eslint-disable-next-line @typescript-eslint/no-this-alias
    let squares: Bigint2048 = this;
    for (let i = 0; i < bits.length; ++i) {
      result = new Bigint2048(
        Provable.if(bits[i], Bigint2048, result.mul(squares), result)
      );
      squares = squares.mul(squares);
    }
    return result;
  }

  // --------------------------------------------------------------------------
  // Comparisons and asserts

  cmp(other: Bigint2048): Field /* in Ordering */ {
    // Handle absolute value
    let state = Field(Ordering.Equal);

    for (let i = LIMB_NUM - 1; i >= 0; --i) {
      state = Provable.switch(
        [
          state.equals(Ordering.Less),
          state.equals(Ordering.Equal),
          state.equals(Ordering.Greater),
        ],
        Field,
        [
          Field(Ordering.Less),
          Provable.switch(
            [
              other.fields[i].greaterThan(this.fields[i]),
              other.fields[i].equals(this.fields[i]),
              other.fields[i].lessThan(this.fields[i]),
            ],
            Field,
            [
              Field(Ordering.Less),
              Field(Ordering.Equal),
              Field(Ordering.Greater),
            ]
          ),
          Field(Ordering.Greater),
        ]
      );
    }

    // Handle sign
    const thisNegative = this.negative.and(this.isZero().not());
    const otherNegative = other.negative.and(other.isZero().not());
    return Provable.switch(
      [
        thisNegative.and(otherNegative.not()),
        thisNegative.not().and(otherNegative),
        thisNegative.not().and(otherNegative.not()),
        thisNegative.and(otherNegative),
      ],
      Field,
      [
        Field(Ordering.Less), // - < +
        Field(Ordering.Greater), // + > -
        // + v + is normal
        state,
        // - v - is flipped
        Provable.switch(
          [
            state.equals(Ordering.Less),
            state.equals(Ordering.Equal),
            state.equals(Ordering.Greater),
          ],
          Field,
          [Field(Ordering.Greater), Field(Ordering.Equal), Field(Ordering.Less)]
        ),
      ]
    );
  }

  isZero(): Bool {
    let state = Bool(true);
    for (let i = 0; i < LIMB_NUM; ++i) {
      state = state.and(this.fields[i].equals(0));
    }
    return state;
  }

  equals(other: Bigint2048): Bool {
    // Simpler than cmp()
    let bothAreZero = Bool(true);
    let allEqual = Bool(this.negative.equals(other.negative));
    for (let i = 0; i < LIMB_NUM; ++i) {
      allEqual = allEqual.and(this.fields[i].equals(other.fields[i]));
      bothAreZero = bothAreZero.and(this.fields[i].equals(0));
      bothAreZero = bothAreZero.and(other.fields[i].equals(0));
    }
    return bothAreZero.or(allEqual);
  }

  lessThan(other: Bigint2048): Bool {
    return this.cmp(other).equals(Ordering.Less);
  }

  lessThanOrEqual(other: Bigint2048): Bool {
    return this.cmp(other).equals(Ordering.Greater).not();
  }

  greaterThan(other: Bigint2048): Bool {
    return this.cmp(other).equals(Ordering.Greater);
  }

  greaterThanOrEqual(other: Bigint2048): Bool {
    return this.cmp(other).equals(Ordering.Less).not();
  }

  assertEquals(other: Bigint2048): void {
    this.equals(other).assertTrue(
      errorMessage(() => `expected ${this} == ${other}`)
    );
  }

  assertNotEquals(other: Bigint2048): void {
    this.equals(other).assertFalse(
      errorMessage(() => `expected ${this} != ${other}`)
    );
  }

  assertLessThan(other: Bigint2048): void {
    this.cmp(other).assertEquals(
      Ordering.Less,
      errorMessage(() => `expected ${this} < ${other}`)
    );
  }

  assertLessThanOrEqual(other: Bigint2048): void {
    this.cmp(other).assertNotEquals(
      Ordering.Greater,
      errorMessage(() => `expected ${this} <= ${other}`)
    );
  }

  assertGreaterThan(other: Bigint2048): void {
    this.cmp(other).assertEquals(
      Ordering.Greater,
      errorMessage(() => `expected ${this} > ${other}`)
    );
  }

  assertGreaterThanOrEqual(other: Bigint2048): void {
    this.cmp(other).assertNotEquals(
      Ordering.Less,
      errorMessage(() => `expected ${this} >= ${other}`)
    );
  }
}

/**
 * x*y mod p
 */
function multiply(
  x: Bigint2048,
  y: Bigint2048,
  p: Bigint2048,
  { isSquare = false } = {}
): Bigint2048 {
  if (isSquare) y = x;

  // witness q, r so that x*y = q*p + r
  // this also adds the range checks in `check()`
  let { q, r } = Provable.witness(
    provable({ q: Bigint2048, r: Bigint2048 }),
    () => {
      let xy = x.toBigInt() * y.toBigInt();
      let p0 = p.toBigInt();
      let q = xy / p0;
      let r = xy - q * p0;
      return { q: Bigint2048.from(q), r: Bigint2048.from(r) };
    }
  );

  // compute delta = xy - qp - r
  // we can use a sum of native field products for each limb, because
  // input limbs are range-checked to LIMB_BITS bits, and 2*LIMB_BITS + log(2*LIMB_NUM-1) fits the native field.
  let delta: Field[] = Array.from({ length: 2 * LIMB_NUM - 1 }, () => Field(0));
  let [X, Y, Q, R, P] = [x.fields, y.fields, q.fields, r.fields, p.fields];

  for (let i = 0; i < LIMB_NUM; i++) {
    // when squaring, we can save constraints by not computing xi * xj twice
    if (isSquare) {
      for (let j = 0; j < i; j++) {
        delta[i + j] = delta[i + j].add(X[i].mul(X[j]).mul(2n));
      }
      delta[2 * i] = delta[2 * i].add(X[i].mul(X[i]));
    } else {
      for (let j = 0; j < LIMB_NUM; j++) {
        delta[i + j] = delta[i + j].add(X[i].mul(Y[j]));
      }
    }

    for (let j = 0; j < LIMB_NUM; j++) {
      delta[i + j] = delta[i + j].sub(Q[i].mul(P[j]));
    }

    delta[i] = delta[i].sub(R[i]).seal();
  }

  // perform carrying on the difference to show that it is zero
  let carry = Field(0);

  for (let i = 0; i < 2 * LIMB_NUM - 2; i++) {
    let deltaPlusCarry = delta[i].add(carry).seal();

    carry = Provable.witness(Field, () => deltaPlusCarry.div(1n << LIMB_BITS));
    rangeCheck128Signed(carry);

    // (xy - qp - r)_i + c_(i-1) === c_i * 2^LIMB_BITS
    // proves that bits i*LIMB_BITS to (i+1)*LIMB_BITS of res are zero
    deltaPlusCarry.assertEquals(carry.mul(1n << LIMB_BITS));
  }

  // last carry is 0 ==> all of diff is 0 ==> x*y = q*p + r as integers
  delta[2 * LIMB_NUM - 2].add(carry).assertEquals(0n);

  return r;
}

/**
 * Custom range check for a single limb, x in [0, 2^LIMB_BITS)
 */
function rangeCheck116(x: Field) {
  // TODO: this function assumes LIMB_BITS=116
  let [x0, x1] = Provable.witnessFields(2, () => [
    x.toBigInt() & ((1n << 64n) - 1n),
    x.toBigInt() >> 64n,
  ]);

  Gadgets.rangeCheck64(x0);
  let [x52] = Gadgets.rangeCheck64(x1);
  x52.assertEquals(0n); // => x1 is 52 bits
  // 64 + 52 = 116
  x0.add(x1.mul(1n << 64n)).assertEquals(x);
}

/**
 * Custom range check for carries, x in [-2^127, 2^127)
 */
function rangeCheck128Signed(xSigned: Field) {
  let x = xSigned.add(1n << 127n);

  let [x0, x1] = Provable.witnessFields(2, () => {
    const x0 = x.toBigInt() & ((1n << 64n) - 1n);
    const x1 = x.toBigInt() >> 64n;
    return [x0, x1];
  });

  Gadgets.rangeCheck64(x0);
  Gadgets.rangeCheck64(x1);

  x0.add(x1.mul(1n << 64n)).assertEquals(x);
}
