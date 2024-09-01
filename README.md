# o1js GCD on 2048-bit numbers

This code benchmarks Eucilidean GCD on 2048-bit numbers using o1js.

With our benchmarks, we get that:

- Up to 9 iterations of GCD can be done before reaching the max circuit size
- GCD of two 2048-bit numbers can take approximately 1hr on modern hardware

## How run

```bash
npm install
npm run runner
```

# Credits

This code is based on [o1js-rsa](https://github.com/Shigoto-dev19/o1js-rsa/)
