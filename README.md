This repository contains companion source code for paper
[Projective Geometry of Hessian Elliptic Curves and Genus 2 Triple Covers of Cubics
](https://eprint.iacr.org/2022/1107) by Rémy Oudompheng.

The code is written in Python using [SageMath](
https://www.sagemath.org)

# Computations used for proofs

File [test_proofs.py](test_proofs.py) contains computations supporting
claims or formulas found in the paper.

# Computation of the gluing map

The main Python files contain code performing the computation
described in the article. The file [gluing_paper.py](gluing_paper.py)
is the exact implementation described in the paper.
The file [gluing3.py](gluing3.py) is intended as a library
and follows more usual coding conventions.

# Comparison with Bröker-Howe-Lauter-Stevenhagen algorithm

Article "Genus 2 curves and Jacobians with a given number of points"
([arXiv/1403.6911](https://arxiv.org/abs/1403.6911))
describes an algorithm solving a related problem (enumerate all possible
gluing for a given pair of elliptic curves).

# Testing

This repository can be tested using `pytest`.

