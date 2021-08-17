Building on yinyang
===================
This section  gives a brief overview of TypeFuzz's implementation and describes how researchers and practitioners can customize and extend TypeFuzz and yinyang.

Understanding TypeFuzz's implementation
...................................................
The following file tree shows the most important files of typefuzz and includes a brief description. 

.. code-block:: text

    yinyang
    ├── bin
    │   └── typefuzz                        - main executable of typefuzz, cli interface
    ├── config
    │   ├── Config.py                       - solver configurations, crash, duplicate, ignore lists
    │   └── typefuzz_config.txt             - typefuzz configuration file 
    ├── src
    │   ├── base                            - contains driver, argument parser, exitcodes, etc.
    │   ├── core
    │   │   └──  Fuzzer.py                  - implements the fuzzing loop and the bug checking oracle
    │   ├── mutators
    |   |   └── GenTypeAwareMutation
    │   │       └── GenTypeAwareMutation.py - mutator integrating generative type-aware mutations
    │   └── parsing
    │       ├── Ast.py                      - classes for scripts, commands, expressions, etc.
    │       ├── Parse.py                    - SMT-LIB v2.6 parser
    │       ├── SMTLIBv2.g4                 - SMT-LIB v2.6 antlr4 grammar
    │       └── Typechecker.py              - SMT-LIB v2.6 type checker
    └── tests                               - contains unit, integration, and regression tests

When TypeFuzz is called from the command line, it executes `bin/typefuzz` containing the main function. After parsing the command line and reading in the seeds, the method `Fuzzer.py:run` is called. It randomly pops an SMT-LIB file from the seed list (`Fuzzer.py:142`), then parses (`Fuzzer.py:98`) and type-checks (`Fuzzer.py:146`) the SMT-LIB file. Next, we compute the set of unique expressions (`Fuzzer.py:148`) from the seed and pass it to a newly created mutator GenTypeAwareMutation (`Fuzzer.py:149`). The mutator is then called in a for-loop realizing n consecutive mutations (`Fuzzer.py:171`). Each mutated formula is then passed to the SMT solvers under test which checks for soundness bugs, invalid model bugs, assertion violations, segfaults (`Fuzzer.py:185`) and dumps the bug triggers to the disk. For details on these checks, read the comments in the method `Fuzzer.py:test`.            

Generative type-aware mutation's mutator class is realized in `GenTypeAwareMutation.py`. It takes a type-checked SMT-LIB script and the set of its unique expressions as arguments to the constructor. Then, we parse the configuration file (`yinyang/config/typefuzz_config.txt`) containing the operator signatures. The method `mutate` implements a mutation step. First, we call the method `get_all_subterms` to return a list of all expressions (`av_expr`) and another list with their types (`expr_type`). Next, we repeatedly choose a term t1 from the formula to be substituted by a term t2 (returned by `get_replacee`). If we could successfully construct such a term, then we substitute and return the mutated formula.

The `get_replacee(term)` method randomly chooses an operator from the list of candidate operators. The list of candidate operators contains all operators with a return type matching term's type and includes the identity operator `id`. Next, we pick a type-conforming expression from the set of unique expressions for every argument for the operator at hand and return the expression. The `get_replacee`method may fail, e.g., if we would have picked an operator of a conforming type but no term with conforming types to its arguments exist. To avoid this, we repeat the `get_replacee` method several times.

Customizing and extending yinyang
...............................................
The yinyang framework has many tests to ensure the reliability of its mutators and the bug detection logic. All tests are integrated into a CI making sure that the bug-finding ability is preserved on every commit. yinyang adheres to the PEP 8 code quality standard. We briefly describe how researchers and practitioners can customize and extend the framework. For an in-depth overview of the yinyang framework, see the [documentation](https://yinyang.readthedocs.io/en/latest/).                 

Run TypeFuzz with other SMT Solvers
....................................
Besides Z3 and CVC4, TypeFuzz can be run with any other SMT solver such as [MathSAT](http://mathsat.fbk.eu), [Boolector](http://verify.inf.usi.ch/content/opensmt2), [Yices](http://yices.csl.sri.com/), and [SMT-Interpol](http://ultimate.informatik.uni-freiburg.de/smtinterpol/), etc. Since TypeFuzz is based on differential testing, it needs at least two solver configurations, ideally with a large overlap in the supported SMT logics. Furthermore, yinyang's type checker currently has stable support for string and arithmetic logics. Support for other logics is currently experimental but will be finalized shortly.

Solver configurations could either be specified in the command line or in the configuration file `yinyang/config/Config.py` such as:  
.. code-block:: text

    solvers = [
        "yices-smt2 --incremental" 
        "z3 model_validate=true",
        "z3 model_validate=true smt.arith.solver=6",
        "cvc4 --check-models --produce-models --incremental --strings-exp -q",
    ]

To run TypeFuzz with these four solver configurations in the config file, you would need to run `typefuzz "" <benchmark-dir>`. Note, the `crash_list` in yinyang/config/config.py, which may need to be updated ensuring that crashes by the new solver(s) are caught.

Devise a custom mutator 
.........................

Fuzzing frameworks such as AFL and others have greatly benefited from the SE/PL community efforts to extend their mutation strategies. In the same spirit, we describe steps on how users can extend yinyang with custom mutators.                

1. Add a new mutator class to `src/mutators`, e.g., `CustomGenerator.py`. A mutator takes a parsed SMT-LIB script as its input and returns the mutated script. The mutation should usually be implemented in a separate mutate method `CustomGenerator.py::mutate()`. For example, consider, `src/mutators/GenTypeAwareMutation/GenTypeAwareMutation.py` or `src/mutators/TypeAwareOpMutation.py`.
2. Provide an executable in the `bin` directory and add parser code to `base/ArgumentParser.py`. 
3. Integrate the mutator in the fuzzing loop in `src/core/Fuzzer.py::run()`.

Extend the input language
..........................

Similar to many PLs, the [SMT-LIB language](https://smtlib.cs.uiowa.edu/language.shtml) is steadily augmented by new features, theories, etc. Furthermore, researchers use SMT-LIB dialects for their solver inputs (e.g. for sygus rewrite rules). To support such use cases, we have based yinyang's parser on an [ANTLR](https://www.antlr.org/) grammar that is simple to customize.

1. Extend grammar `src/parsing/SMTLIBv2.g4`.
2. Regenerate the grammar using `src/parsing/regenerate_grammar.sh`.
3. Extend parse tree visitor `src/parsing/AstVisitor.py` and AST implementation `src/parsing/Ast.py`.
4. If type checking is needed, augment the type checker in `src/parsing/Typechecker.py`.    


Citing yinyang 
.................

The testing approaches implemented in yinyang are based on following two papers.

**Type-Aware Operator Mutation (opfuzz)** `[pdf] <https://dl.acm.org/doi/abs/10.1145/3428261>`__

.. code-block:: latex 

    @article{winterer-zhang-su-oopsla2020
      author    = {Dominik Winterer and
                   Chengyu Zhang and
                   Zhendong Su},
      title     = {On the unusual effectiveness of type-aware operator mutations for
                   testing {SMT} solvers},
      journal   = {Proc. {ACM} Program. Lang.},
      volume    = {4},
      number    = {{OOPSLA}},
      pages     = {193:1--193:25},
      year      = {2020},
    }


**Semantic Fusion (fusion)**  `[pdf] <https://dl.acm.org/doi/abs/10.1145/3385412.3385985>`__

.. code-block:: latex 

    @inproceedings{winterer-zhang-su-pldi2020,
          title = {Validating SMT Solvers via Semantic Fusion},
          author = {Winterer, Dominik and Zhang, Chengyu and Su, Zhendong},
          year = {2020},
          booktitle = {Proceedings of the 41st ACM SIGPLAN Conference on Programming 
                       Language Design and Implementation},
          pages = {718–730}
    }


Contact
........
We are always happy to receive your feedback or help you adjust yinyang to the needs of your custom solver, help you build on yinyang, etc. Reach out for us.

* `Dominik Winterer <https://wintered.github.io/>`_ - dominik.winterer@inf.ethz.ch

* `Chengyu Zhang <http://chengyuzhang.com/>`_ - dale.chengyu.zhang@gmail.com

* `Jiwon Park <https://www.linkedin.com/in/jiwon-park-473998170/?originalSubdomain=fr>`_ - jiwon.park@polytechnique.edu  

* `Zhendong Su <https://people.inf.ethz.ch/suz/>`_ - zhendong.su@inf.ethz.ch 
