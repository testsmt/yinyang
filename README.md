<p align="center"><a><img width="130" alt="portfolio_view" align="center" src="media/logo.png"></a></p>

___________
[![Build Status](https://github.com/testsmt/yinyang_private/workflows/ci/badge.svg)](https://github.com/testsmt/yinyang_private/actions)
[![Documentation Status](https://readthedocs.org/projects/yinyang/badge/?version=latest)](https://yinyang.readthedocs.io/en/latest/?badge=latest)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Twitter](https://img.shields.io/twitter/follow/testsmtsolvers?style=social)](https://twitter.com/testsmtsolvers)


A fuzzer for SMT solvers. Given a set of seed SMT formulas, yinyang generates mutant formulas to stress-test SMT solvers. yinyang can be used to robustify SMT solvers. It already found **1,000+** bugs in the two state-of-the-art SMT solvers Z3 and CVC4.



Installation
------------
Requirements: 
- python 3.6+ 
- antlr4 python runtime  
``` bash
git clone https://github.com/testsmt/yinyang.git 
pip3 install antlr4-python3-runtime==4.8  
```


Usage
-------------
1. **Get SMT-LIB 2 benchmarks**. Edit `scripts/SMT-LIB-clone.sh` to select the logics for testing. Run `./scripts/SMT-LIB-clone.sh`
to download the corresponding SMT-LIB 2 benchmarks. Alternatively, you can download benchmarks directly from the [SMT-LIB website](http://smtlib.cs.uiowa.edu/benchmarks.shtml) or supply your own benchmarks. 

2. **Get and build SMT solvers** for testing. Install two or more [SMT solvers](http://smtlib.cs.uiowa.edu/solvers.shtml) that support the SMT-LIB 2 format. You may find it convenient to add them to your PATH. 

3. **Run yinyang** on the benchmarks e.g. with Z3 and CVC4.  
```bash
python3 yinyang.py "z3 model_validate=true;cvc4 --check-models -m -i -q" benchmarks 
```

yinyang will by default randomly select formulas from the folder `./benchmarks` and generate 300 mutants per seed formula. If a bug has been found, the bug trigger is stored in `./bugs`. yinyang will run in an infinite loop. You can use the shortcut CTRL+C to terminate yinyang manually.

:blue_book: [Documentation](https://yinyang.readthedocs.io/en/latest/)

Feedback
---------
For bugs/issues/questions/feature requests please file an issue. We are always happy to receive your feedback or help you adjust yinyang to the needs of your custom solver.
 
 :memo: [Contact us](docs/Contributors.md)

Additional Ressources
----------
- [Citing yinyang](docs/Citation.md)
- [Project website](https://testsmt.github.io/) with bug statistics, talk videos, etc.
