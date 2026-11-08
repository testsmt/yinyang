Customization
=============

Options 
.........

yinyang provides the following options. Please consult ``typefuzz --help`` for a full list.

* ``-i --iterations ITERATIONS`` the number of iterations on each seed. (default: 300)  
* ``-m --modulo MODULO`` specifies how often the mutants will be forwarded to the SMT solvers. For example, with 300 iterations and 2 as a modulo, 150 mutants per seed file will be passed to the SMT solvers. High modulo and iteration counts prioritize deeper mutations. (default: 2) 
* ``-t --timeout TIMEOUT`` imposes a timeout limit (in seconds) on each SMT solver for solving  mutant formula. (default: 8) 
* ``--consecutive-timeouts N`` skips the rest of a seed after ``N`` consecutive mutants on which a solver timed out, ``0`` never skips. The mutants of a seed that is hard for a solver mostly time out as well, so the time is better spent on other seeds. (default: 2)
* ``-d, --diagnose`` forwards solver outputs to stdout e.g. for solver command line diagnosis. 
* ``-bugs BUGSFOLDER`` (default: ./bugs) 
* ``-scratch SCRATCHFOLDER`` specifies where the mutant formulas are temporarily stored. Note, if you run yinyang with several processes in parallel, each instance should have its own scratch folder. (default: ./scratch)      
* ``-km --keep-mutants`` do not delete the mutants from the scratch folder. Warning: beware that this can quickly exhaust your entire disk space.
* ``-g, --generate-functions`` dimension of the fusion functions to generate, if greater than 0 do not take into account --config option. (default: 0)
* ``-m, --multiple-variables`` try to fuse at least vars variables, if possible, distributing the variables evenly as possible between the seeds (default: 2)
* ``-q --quiet`` do not output statistics and other output.
* ``-L, --file-size-limit`` skip seeds of this size in bytes or larger. They are counted as invalid seeds and listed in the log. (default: 100000)
* ``--seed`` random seed for reproducible runs. Runs with the same seed, seed files and options generate the same mutants.
* ``--logic-mode`` how to handle the set-logic command of the seeds: ``widen`` keeps the seed's logic and widens it if a mutant needs more, ``skip`` keeps the seed's logic and skips mutants that need more, ``strip`` removes set-logic from all mutants. (default: widen)
* ``--div-by-zero`` how to handle mutants that divide by a literal zero, e.g. ``(/ x 0.0)`` or ``(mod x 0)``. Division by zero is undefined in SMT-LIB, and solvers disagree on whether such terms are linear. ``nonlinear`` makes them need a non-linear logic, as in cvc5 (see ``--logic-mode``), ``linear`` treats them as linear, as in z3, ``skip`` skips them. (default: nonlinear)
* ``--random-all``, ``--no-random-all`` whether to use ``(set-logic ALL)`` instead of the mutant's logic for half of the mutants, so that the solvers are also tested with their configuration for ALL. Logics that yinyang does not understand, e.g. ``HORN``, are kept, and so is the logic of scripts that declare a sort that is built in under ALL, e.g. ``Set`` in z3. (default: on)
* ``--cvc5-compat`` avoid scripts that are valid SMT-LIB but rejected by cvc5 (checked with cvc5 1.4.2), so that no mutant is wasted on them. z3 accepts all of them, so the option is off by default. It handles two restrictions of cvc5:

  * The arguments of ``re.range`` must be ground, e.g. ``(re.range x "c")`` gives ``expecting a constant string term in regexp range``. Ground terms such as ``(str.from_code 97)`` are accepted.
  * Constants of sort ``RegLan`` must be eliminated by cvc5's preprocessing, otherwise cvc5 reports ``Regular expression variables are not supported``. A ``RegLan`` constant that occurs in an assertion must be defined by a top-level equation ``(= r t)`` (also as a conjunct of a top-level ``and``) in which ``r`` does not occur in ``t`` once the other ``RegLan`` constants are substituted. Equations under ``or``, ``ite`` or ``not``, ``distinct``, cyclic definitions such as ``(= r (re.* r))``, quantified ``RegLan`` variables and functions with arguments and range ``RegLan`` are rejected.

  With the option, seeds that violate these restrictions are skipped, typefuzz and opfuzz undo a mutation that violates them and mutate elsewhere, and other mutants that violate them (e.g. from SemanticFusion) are skipped. cvc5 still answers some of these scripts, when it finds a conflict before it reaches the unsupported term.



Customize solvers configurations  
.................................
If you want to test several SMT solver configurations at once the putting them  as a commandline argument like ``typefuzz "<solver_clis>" <seed_path>`` may be inconvenient to you. Instead, you can modify the solver list in ``.yinyang/Config.py``. The directory file need to be created by the user.   

As an example consider:

.. code-block:: python3

    solvers = [                                                                        
        "z3 model_validate=true",                                               
        "z3 model_validate=true smt.arith.solver=2",                            
        "z3 model_validate=true smt.arith.solver=3",                            
        "z3 model_validate=true smt.arith.solver=6",                            
        "cvc4 --check-models --produce-models --incremental --strings-exp -q",         
    ] 

You can then use ``typefuzz "" <seed_path>`` to run the above five solver configurations.


Customize bug detection  
.........................
yinyang's bug detection logic is based on three lists: ``crash_list, duplicate_list, ignore_list`` of ``.yinyang/Config.py`` which you can customize. yinyang detects crash bugs by matching the stdout and stderr of the solvers in with the strings in the list``crash_list``. If yinyang detects a bug this way, it subsequently matches the crash message against all strings in ``duplicate_list``. The ``duplicate_list`` is useful to filter out repeatedly occurring bugs from getting copied to ``./bugs``.  The ``ignore_list`` can be used to filter out errors occurring in a solver call.  By default yinyang detects mutants returning non-zero exit codes as crashes except those that match with the ``ignore_list``.        


The below setup shows the three lists in ``.yinyang/Config.py`` that worked well in practice with Z3 and CVC4. 

.. code-block:: python3

    crash_list = [
        "Exception",
        "lang.AssertionError",
        "lang.Error",
        "runtime error",
        "LEAKED",
        "Leaked",
        "Segmentation fault",
        "segmentation fault",
        "segfault",
        "ASSERTION",
        "Assertion",
        "Fatal failure",
        "Internal error detected",
        "an invalid model was generated",
        "Failed to verify",
        "failed to verify",
        "ERROR: AddressSanitizer:",
        "invalid expression",
        "Aborted"
    ]

    duplicate_list = [

    ]

    ignore_list = [
       "(error ",
        "unexpected char",
        "failed to open file",
        "Expected result sat but got unsat",
        "Expected result unsat but got sat",
        "Parse Error",
        "Cannot get model",
        "Symbol 'str.to-re' not declared as a variable",
        "Symbol 'str.to.re' not declared as a variable",
        "Unimplemented code encountered",
    ]
