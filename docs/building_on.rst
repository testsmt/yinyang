Building on yinyang
===================

Project structure
....................

The following tree shows the most important files of the project and includes a description thereof.

.. code-block:: text
    
    .
    ├── config                                  
    │   ├── config.py                   - solver configurations, crash, duplicate, ignore lists 
    │   ├── fusion_functions.txt        - fusion functions 
    │   ├── operator_mutations.txt      - operators used by the opfuzz
    │   └── option_setting.txt          - options used for option fuzzing   
    ├── docs                            - documentation
    ├── examples                        - small SMT-LIB example formulas
    ├── scripts                         - third-party scripts 
    ├── src                                     
    │   ├── args.py                     - commandline parser 
    │   ├── generators                      
    │   │   ├── Generator.py            - generic generator class 
    │   │   ├── SemanticFusion
    │   │   │   ├── SemanticFusion.py   - generator for fusion
    │   │   │   ├── VariableFusion.py   - variable fusion, template filling         
    │   │   │   └── util.py             - conjunction and disjunction of formulas,etc.
    │   │   └── TypeAwareOpMutation.py  - generator for opfuzz 
    │   ├── modules
    │   │   ├── Fuzzer.py               - implements fuzzing loop    
    │   │   ├── OptionGenerator.py      - implements option fuzzing
    │   │   ├── Solver.py               - calls SMT solvers  
    │   │   ├── Statistic.py            - fuzzing statistics 
    │   ├── parsing
    │   │   ├── SMTLIBv2.g4             - antlr SMT-LIB grammar
    │   │   ├── ast.py                  - AST implementation 
    │   │   ├── ast_visitor.py          - generates AST from parse tree    
    │   │   ├── parse.py                - parse SMT-LIB from file/string
    │   │   ├── regenerate_grammar.sh   - script to regenerate SMT-LIB grammar   
    │   │   └── util.py
    │   └── utils.py
    ├── tests                                   
    │   ├── integration_tests           - opfuzz sanity checks, bug detection etc.          
    │   └── unittests                   - regular unittests   
    └── yinyang.py

Devise a custom mutation strategy 
..................................

1. Add a new generator class to ``src/generators``, e.g., ``CustomGenerator.py``. A generator takes a path to a single SMT-LIB in its constructor, parses the corresponding SMT-LIB file into a Script object, and returns the mutated Script class. The mutation should usually be implemented in a separate generate method, e.g. ``CustomGenerator.py::generate()``. For an example, consider ``src/generators/TypeAwareOpMutation.py``.                

2. Add strategy to commandline option argument ``--strategy`` in ``src/args.py``.    

3. Integrate the generator in the fuzzing loop in ``src/modules/Fuzzer.py::run()``.     


Extend the input language 
................................
1. Extend grammar ``src/parsing/SMTLIBv2.g4``.   
2. Regenerate the grammar using ``regenerate_grammar.sh``.
3. Extend parse tree visitor ``src/parsing/ast_visitor.py`` and AST implementation ``src/parsing/ast.py``.  


Use yinyang as an SMT-LIB parser 
..................................
The following example shows how you can use yinyang as an SMT-LIB parser.  

.. code-block:: python3 

    from src.parsing.ast import *
    from src.parsing.parse import *
    formula=\
    """
    (declare-fun x () Int)
    (declare-fun y () Int)
    (declare-fun z () Int)
    (assert (> (* (+ 3 x) (- y 2)) (/ 5 z)))
    (check-sat)
    """

    formula, glob = parse_str(formula)



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

* `Zhendong Su <https://people.inf.ethz.ch/suz/>`_ - zhendong.su@inf.ethz.ch 
