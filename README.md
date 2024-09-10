# P PBT
Property-Based Testing For P

# Install

The easiest way to install the dependencies is via [OPAM](https://opam.ocaml.org/doc/Install.html).

```
  opam init --auto-setup
  opam update
  opam switch create PPBT --package=ocaml-variants.4.14.1+options,ocaml-option-flambda
  eval $(opam env)
  opam install dune core core_unix yojson conf-c++ conf-python qcheck ocolor dolog ocamlbuild z3 ppx_deriving_yojson menhirLib menhir
```

The download the dependent library: https://github.com/zhezhouzz/language_utils, then install it.

```
    cd language_utils
    opam install .
```

Then compile this repo:

```
    dune build
```

# Run Synthesizer

```
    python3 script/run_bench.py [path to TestExamples-PTestGeneration] [command] [benchmark name] [spec name] (verbose)
```

The supported benchmarks and specs are shown in `benchmarks`.
Add `verbose` can print the actual shell commands.
Currently, please set `command` as `random-p-sfa` to generate random client.

For example,

```
    python3 script/run_bench.py ~/workplace/zzws/src/TestExamples-PTestGeneration random-p-sfa ClockBoundFormalModels ClockBoundInvariants
```

A script run all cases:

```
    ./script/run.sh
```

# Run P

Goto corresponding folder with the same name as benchmark name in `TestExamples-PTestGeneration` repo.

```
    p compile && p check -tc Syn
```

The generated code are in `PSyn` folder, structured as following:

```
PSyn
├── Library.p
├── SynClient.p
├── SynDriver.p
└── Warapper.p
```

+ `SynClient.p`: output of synthesizer.
+ `Library.p`: auxiliary functions used by synthesized client machines in `SynClient.p`.
+ `Warapper.p`: A wrapper convert messages into the format can be recognized by P Model.
+ `SynDriver.p`: test driver and script for synthesized client machines.

