# Self-Initializing Quadratic Sieve (SIQS)

An implementation of the Self-Initializing Quadratic Sieve written in Julia for integer factorization.

## Description

Implementation

- Single Threaded
- Single Large Prime Variation
- Null Space Extraction using Gaussian Elimination over GF(2)
- Self Initialization for Polynomials
- Automatic Parameter Selection
- Tested/Limited to 100 digits
- Validates Input (test for prime number, integer power)
- Uses Pollard Rho Algorithm for Input <= 18 digits


## Performance

|Decimal digits|Duration|
|:--:|:--:|
|30|158 milliseconds|
|60|5 seconds|
|80|6 minutes 36 seconds|
|100|9 hours|

## License

MIT No Attribution
