# Generic Group Analyzer Unbounded

Generic Group Analyzer Unbounded is a tool to automatically prove computational security statements in the [Generic Group Model](https://en.wikipedia.org/wiki/Generic_group_model). It is especially designed to deal with security experiments where the attacker is allowed to interact with an Oracle an **unbounded** number of times and this interaction may be adaptive, i.e., new queries can depend on earlier Oracle responses.

We refer to our paper [https://eprint.iacr.org/2016/270](https://eprint.iacr.org/2016/270) for more details.

## Installation

*1*. Install [Opam](https://opam.ocaml.org/).

 * In Ubuntu,

~~~~~
apt-get install -y ocaml ocaml-native-compilers opam libtool libtool-bin libgmp-dev libffi-dev m4 libz-dev libssl-dev camlp4-extra
~~~~~

 * In OS X, use homebrew,

~~~~~
brew install opam
~~~~~

*2*. Install the right compiler and the right libraries.

~~~~~
opam pin add gga-unbounded GGA_UNBOUNDED_DIR -n
opam install gga-unbounded --deps-only
~~~~~

*3*. The tool uses [Sage](http://www.sagemath.org/) and [Z3](https://z3.codeplex.com/) as backend.

 * For Sage, you should be able to start 'sage -python'. (We used SageMath, Version 6.8).

 * We use a Z3 wrapper written in Python. Visit the [Z3 GitHub project](https://github.com/Z3Prover/z3).

*4*. Set the path variable:

~~~~~
export UBT_PATH=GGA_UNBOUNDED_DIR
~~~~~

*5*. To compile the tool use 'make'. This will produce two executables: 

 * **ubt.native** to perform automated analysis.

 * **wsubt.native** to communicate via web sockets with the interactive tool.

*6*. (Interactive Mode) The interactive mode uses [MathJax](https://www.mathjax.org/). You can install it, by changing to the web directory, i.e., 'cd web/' and running 'make get-mathjax'.


## Usage

#### Input files

The description of the cryptographic construction and the security game is provided to the tool as an input file. As an example, we present the input file Chatterjee-Menezes.ubt expressing the Structure-Preserving Scheme described in [this paper](https://eprint.iacr.org/2014/635) and the EUC-CMA security experiment: 

~~~~~
group_setting 3.

sample V,W.

input [V,W] in G1.

oracle o1(M:G2) =
  sample R;
  return [ R ] in G1,
         [ R, M*V + R^2 + W] in G2.

win (wM:G2, wR1:G1, wR2:G2, wS:G2) =
    (forall i: wM <> M_i /\ wR1 = wR2 /\ wS = V*wM + wR1*wR2 + W).
~~~~~

#### Automated mode

You can use the automated algorithm by running, e.g.:

~~~~~
./ubt.native examples/Automatic/Chatterjee-Menezes.ubt
~~~~~

This will produce the following output,

~~~~~
simplify.
extract_coeffs.
simplify.
simplify.
case_distinction p9_j'1.
  simplify.
  contradiction.
simplify.
divide_by_param p9_i'1.
simplify.
contradiction.
Proven!
Time 3.49 seconds
~~~~~

which corresponds to the sequence of commands that the automatic algorithm executed to prove the security of the cryptographic scheme. Visit the [Documentation](http://generic-group-analyzer.github.io/gga-ub/index.html) for details about these commands.

See [examples/Automatic/](https://github.com/generic-group-analyzer/gga-unbounded/tree/master/examples/Automatic) for more examples.

To reproduce our results, execute 'cd examples/ && ./test.sh'.

#### Interactive mode

We provide an interactive web interface where you can execute commands while watching the current state of the proof. This can be used to analyze given proofs or to produce customized ones.

To start the web interface, execute:

~~~~~
./wsubt.native examples/Interactive/Chatterjee-Menezes.ubt
~~~~~

and open the shown URL in your browser,

~~~~~
Open the following URL in your browser (websocket support required):

    file:///GGA_UNBOUNDED_DIR/web/index.html

Files: examples/Interactive/Chatterjee-Menezes.ubt
~~~~~