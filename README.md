# Introduction to the Theory of Computation

The Turing project aims to offer the foundations of the Theory of Computation
formalized in Coq. This includes results on
* Formal languages: common operators and language equality results
* Regular languages: regular expressions, pumping lemma
* Turing machines: acceptance, equality, map-reducibility, decidability.


This project is led by [Tiago Cogumbreiro](https://cogumbreiro.github.io/) to
support teaching an undergraduate course on Theory of Computing, [CS 420, at UMass
Boston](https://www.umb.edu/course_catalog/course_info/ugrd_CS_all_420). See
Tiago's [archives of Fall'20](https://cogumbreiro.github.io/teaching/cs420/s20/)
to access the teaching material.

# Installation

## Windows

```
$ scoop install https://gitlab.com/cogumbreiro/turing/-/raw/master/scoop/turing.json
```

## Unix-based OS


To install the Turing library in your system run these commands:
```bash
$ git clone https://gitlab.com/cogumbreiro/turing
$ cd turing
$ ./configure.sh
$ make
$ make install
```

# Updating

**Make sure you have already installed `Turing` in your system.**

## Windows

```bash
> scoop update turing
```

## Unix-based OS

Then, run the following commands:

```bash
$ cd /path/where/you/installed/turing
$ git pull
$ make
$ make install
```


# Coverage

In this project, we are formalizing some content of the book Introduction to the
textbook Theory of Computation, by Michael Sipser, 3<sup>rd</sup> edition.

## Chapter 1: `Regular.v`
* [x] Theorem 1.70: Pumping lemma for regular languages
* [x] Example 1.73: $`\{ 0^n 1^n \mid n \ge 0 \}`$ is not regular

## Chapter 4: `LangDec.v`
* [x] Theorem 4.11: $`A_{\mathsf{TM}}`$ is undecidable.
* [x] Corollary 4.18: Some languages are not recognizable.
* [x] Theorem 4.22: $`L`$ is decidable iff $`L`$ is recognizable and co-recognizable
* [x] Theorem 4.23: $`\overline{A}_{\mathsf{TM}}`$ is not recognizable.

## Chapter 5: `LangRed.v`
* [x] Theorem 5.1: $`HALT_{\mathsf{TM}}`$ is undecidable.
* [x] Theorem 5.2: $`E_{\mathsf{TM}}`$ is undecidable.
* [x] Theorem 5.4: $`EQ_{\mathsf{TM}}`$ is undedicable.
* [x] Theorem 5.22: If $`A \le_{\mathrm{m}} B`$ and $`A`$ decidable, then $`B`$ decidable.
* [x] Theorem 5.28: If $`A \le_{\mathrm{m}} B`$ and $`A`$ recognizable, then $`B`$ recognizable.
* [x] Corollary 5.29: If $`A \le_{\mathrm{m}} B`$ and $`B`$ is undecidable, then $`A`$ is undecidable.
* [x] Corollary 5.30: $`EQ_{\mathsf{TM}}`$ unrecognizable and co-unrecognizable.
