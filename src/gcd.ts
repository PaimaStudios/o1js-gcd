import { Bool, Provable, SelfProof, Struct, ZkProgram } from 'o1js';
import { Bigint2048 } from './bigint';

export const GCD_ITERATIONS_PER_PROOF = 9;

export class GcdPair extends Struct({
  g_0: Bigint2048,
  g_1: Bigint2048,
}) {
  isSolved(): Bool {
    const subGcd = this.g_0.equals(this.g_1);
    const divGcd = this.g_1.equals(Bigint2048.ZERO);
    return subGcd.or(divGcd);
  }
  assertSolved(): { g: Bigint2048 } {
    this.isSolved().assertTrue();
    return {
      g: this.g_0,
    };
  }

  euclidGcd(): GcdPair {
    const curr = new GcdPair(this);
    for (let i = 0; i < GCD_ITERATIONS_PER_PROOF; ++i) {
      const isZero = curr.g_1.equals(Bigint2048.ZERO);

      // a %= b
      [curr.g_0, curr.g_1] = [
        new Bigint2048(Provable.if(isZero, Bigint2048, curr.g_0, curr.g_1)),
        new Bigint2048(
          Provable.if(
            isZero,
            Bigint2048,
            curr.g_1,
            curr.g_0.floorDiv(
              new Bigint2048(
                Provable.if(
                  curr.g_1.equals(Bigint2048.ZERO),
                  Bigint2048,
                  Bigint2048.ONE,
                  curr.g_1
                )
              )
            ).rem
          )
        ),
      ];
    }

    return curr;
  }
}
export const GcdProgram = ZkProgram({
  name: 'gcd',
  publicInput: GcdPair,
  publicOutput: GcdPair,
  methods: {
    baseCase: {
      privateInputs: [],

      async method(publicInput: GcdPair) {
        return publicInput.euclidGcd();
      },
    },

    step: {
      privateInputs: [SelfProof],

      async method(
        publicInput: GcdPair,
        earlierProof: SelfProof<GcdPair, GcdPair>
      ) {
        earlierProof.verify();
        publicInput.g_0.assertEquals(earlierProof.publicInput.g_0);
        publicInput.g_1.assertEquals(earlierProof.publicInput.g_1);
        return earlierProof.publicOutput.euclidGcd();
      },
    },
  },
});
