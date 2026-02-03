[![Logo for Axiom Math](logo.svg)](https://axiommath.ai/)

# Almost all primes are partially regular

These files accompany the paper [arXiv:TODO](TODO).

The formal proofs provided in this work were developed and verified using **Lean 4.26.0**. Compatibility with earlier or later versions is not guaranteed due to the evolving nature of the Lean 4 compiler and its core libraries.

## Input files

- `problem.tex`: natural language description of the problem
- `.environment`: specifies the Lean version

## Output files (Run with Lean 4.26.0)

- `problem.lean`: translation of the problem statement into formal language (Lean)
- `solution.lean`: solution in formal language (Lean)

## Additional files

Besides the end-to-end run above, we internally also conducted experiments
where we provided AxiomProver with additional tools,
such as [AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
(although this dependency ended up not being needed).
In one of these experiments, AxiomProver found that
actually $C_{\alpha} = 10$ works for all $\alpha > 1/2$.

We provide the corresponding Lean files in `extension/`.

## License

This repository uses the MIT License. See [LICENSE](LICENSE) for details.

## Repository maintainers

- [Evan Chen](https://github.com/vEnhance)
- [Kenny Lau](https://github.com/kckennylau)
- [Seewoo Lee](https://github.com/seewoo5)
- [Ken Ono](https://github.com/kenono691)
- [Jujian Zhang](https://github.com/jjaassoonn)
