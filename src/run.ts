import { GCD_ITERATIONS_PER_PROOF, GcdPair, GcdProgram } from './gcd.js';
import { Bigint2048 } from './bigint.js';

const forceRecompileEnabled = false;

{
  // const pair = new GcdPair2({ g_0: Bigint2048.from(48n), g_1: Bigint2048.from(18n) });
  const pair = new GcdPair({
    g_0: Bigint2048.from(
      66192067702349471902822889917521630986608145681764058902797324107655626550548394747593124784626505148515147440884312503123977915307410797250481114283716893992887254383889295241096466408449603762914352825104572615207366531086433177129596279528363570312063132413328722950462592090559000063264135584309478448349n
    ),
    g_1: Bigint2048.from(
      64994285377340214206572207534835868053851007183284265013844951369449810556767127886232672704240625827623339904466957865609336308250664600055526550318867746860900055215309858041282435305032854457866704943529828131858657354140245647370594766415054469927382930751337852515318596998217230438351735326293886615645n
    ),
  });

  console.time('compile');
  await GcdProgram.compile({ forceRecompile: forceRecompileEnabled });
  console.timeEnd('compile');

  console.time('GCD');
  {
    console.log('input=', JSON.stringify(pair));

    let currTime = new Date().getTime();
    // let proof = await GcdProgram.start(pair);
    let proof = await GcdProgram.baseCase(pair);

    console.log(`iter 1: ${new Date().getTime() - currTime}`);
    currTime = new Date().getTime();

    let i = 1;
    while (!proof.publicOutput.isSolved().toBoolean()) {
      console.log('progress=', JSON.stringify(proof.publicOutput));
      proof = await GcdProgram.step(pair, proof);
      console.log(`iter ${i + 1}: ${new Date().getTime() - currTime}`);
      currTime = new Date().getTime();
      ++i;
    }
    console.log('final progress=', JSON.stringify(proof.publicOutput));
    console.log(
      i,
      '*',
      GCD_ITERATIONS_PER_PROOF,
      'iters for gcd(',
      pair.g_0.toBigInt(),
      ', ',
      pair.g_1.toBigInt(),
      ')'
    );
    console.log(`Proof: `, proof);
    console.log('Solution: ', proof.publicOutput.assertSolved().g.toBigInt());
  }
  console.timeEnd('GCD');
}
